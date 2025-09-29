---- MODULE MCProgram ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets
\* LOCAL INSTANCE MCLayout
LOCAL INSTANCE TLC

VARIABLES globalVars, threadLocals, state, DynamicNodeSet, globalCounter

(* Layout Configuration *)

Threads == {tid : tid \in 1..NumThreads}

(* Variable *)
Var(varScope, varName, varValue, index) == 
    [scope |-> varScope,
     name  |-> varName, 
     value |-> varValue,
     index |-> index]

Index(idx) == 
    [realIndex |-> idx]

IsVar(var) ==
    /\ "scope" \in DOMAIN var 
    /\ "name" \in DOMAIN var 
    /\ "value" \in DOMAIN var
    /\ "index" \in DOMAIN var

IsArray(var) ==
    /\ IsVar(var)
    /\ var.index.realIndex >= 0

\* We do it only to make TLC happy, as index could be an expression
IsIndex(var) ==
    /\ "realIndex" \in DOMAIN var

IsLiteral(var) ==
    /\ IsVar(var)
    /\ var.scope = "literal"

IsLocal(var) ==
    /\ IsVar(var)
    /\ var.scope = "local"

IsShared(var) ==
    /\ IsVar(var)
    /\ var.scope = "shared"

IsGlobal(var) ==
    /\ IsVar(var)
    /\ var.scope = "global"

IsVariable(var) ==
    \/ IsLocal(var)
    \/ IsShared(var)
    \/ IsGlobal(var)

IsIntermediate(var) ==
    /\ IsVar(var)
    /\ var.scope = "intermediate"


GlobalInvocationId(tid) == tid-1

LocalInvocationId(tid) == GlobalInvocationId(tid) % WorkGroupSize

WorkGroupId(tid) == GlobalInvocationId(tid) \div WorkGroupSize
    
SubgroupId(tid) == LocalInvocationId(tid) \div SubgroupSize

SubgroupInvocationId(tid) == LocalInvocationId(tid) % SubgroupSize

ThreadsWithinWorkGroup(wgid) ==  {tid \in Threads : WorkGroupId(tid) = wgid}

ThreadsWithinWorkGroupNonTerminated(wgid) ==  {tid \in Threads : WorkGroupId(tid) = wgid /\ state[tid] # "terminated"}

ThreadsWithinSubgroup(sid, wgid) == {tid \in Threads : SubgroupId(tid) = sid} \intersect ThreadsWithinWorkGroup(wgid)

ThreadsWithinSubgroupNonTerminated(sid, wgid) == {tid \in Threads : SubgroupId(tid) = sid /\ state[tid] # "terminated"} \intersect ThreadsWithinWorkGroup(wgid)

NumSubgroupsPerWorkgroup == WorkGroupSize \div SubgroupSize

(* Expression *)

Inter(S) ==
  { x \in UNION S : \A t \in S : x \in t }
Range(f) == { f[x] : x \in DOMAIN f }
Max(S) == CHOOSE s \in S : \A t \in S : s >= t
Min(S) == CHOOSE s \in S : \A t \in S : s <= t
MinIndices(s, allowedIndices) ==
    LET allowedValues == {s[i] : i \in DOMAIN s \cap allowedIndices}
        minVal == IF allowedValues = {} THEN 1000
                  ELSE Min(allowedValues)
    IN {i \in DOMAIN s \cap allowedIndices : s[i] = minVal}

Push(seq, x) ==
    Append(seq, x)

\* For simplicity we can pop an empty stack
\* Which will be a noop
Pop(seq) == 
  SubSeq(seq, 1, Len(seq)-1)


PopUntilBlock(seq, blockIdx) == 
    LET idxSet == {i \in DOMAIN seq : seq[i].blockIdx = blockIdx}
    IN
        IF idxSet = {} THEN
            seq
        ELSE
            SubSeq(seq, 1, Max(idxSet) - 1)

VarExists(workgroupId, var) == 
    \* IF IsShared(var) \/ IsGlobal(var) THEN 
    IF IsGlobal(var) THEN 
        \E variable \in globalVars : variable.name = var.name 
    ELSE 
        \E variable \in threadLocals[workgroupId] : (variable.name = var.name /\ variable.scope = var.scope)


(* todo: resolve scope if duplicate name *)
GetVar(workgroupId, var) == 
    IF IsGlobal(var) THEN 
        CHOOSE variable \in globalVars : variable.name = var.name 
    ELSE 
        CHOOSE variable \in threadLocals[workgroupId]: (variable.name = var.name /\ variable.scope = var.scope)

\* only mangling local and intermediate variables
Mangle(t, var) ==
    IF var.scope = "local" THEN
        Var(var.scope, Append(ToString(t), Append(var.scope, var.name)), var.value, var.index)
    ELSE IF var.scope = "shared" THEN
        Var(var.scope, Append(ToString(WorkGroupId(t)), Append(var.scope, var.name)), var.value, var.index)
    ELSE IF var.scope = "intermediate" THEN
        Var(var.scope, Append(ToString(t), Append(var.scope, var.name)), var.value, var.index)
    ELSE
        var
    
GetVal(workgroupId, var) == 
    IF IsLiteral(var) THEN
        var.value
    ELSE IF VarExists(workgroupId, var) THEN
        IF IsArray(var) /\ var.index > 0 THEN
            GetVar(workgroupId, var).value[var.index]
        ELSE
            GetVar(workgroupId, var).value
    ELSE 
        /\  Print("Don't has such variable", var)
        /\  FALSE
    
(* Binary Expr *)

\* Mimic Lazy evaluation
BinaryExpr(Op, lhs, rhs) == 
    [operator |-> Op,
     left |-> lhs,
     right |-> rhs]

LessThan(lhs, rhs) == lhs < rhs
LessThanOrEqual(lhs, rhs) == lhs <= rhs
GreaterThan(lhs, rhs) == lhs > rhs
GreaterThanOrEqual(lhs, rhs) == lhs >= rhs
Equal(lhs, rhs) == lhs = rhs
NotEqual(lhs, rhs) == lhs /= rhs
Plus(lhs, rhs) == lhs + rhs
Minus(lhs, rhs) == lhs - rhs
Multiply(lhs, rhs) == lhs * rhs
Indexing(lhs, idx) == lhs[idx]

BinarOpSet == {"LessThan", "LessThanOrEqual", "GreaterThan", "GreaterThanOrEqual", "Equal", "NotEqual", "Plus", "Minus", "Multiply", "Indexing"}

IsBinaryExpr(expr) ==
    IF IsVar(expr) = TRUE THEN
        FALSE
    ELSE
        /\ "operator" \in DOMAIN expr
        /\ "left" \in DOMAIN expr
        /\ "right" \in DOMAIN expr
        /\ expr["operator"] \in BinarOpSet


(* Unary Expr *)
UnaryExpr(Op, rhs) == [operator |-> Op, right |-> rhs]

Not(rhs) ==
    /\  IF rhs = FALSE THEN 
            TRUE
        ELSE
            FALSE 
Neg(rhs) == -rhs

UnaryOpSet == {"Not", "Neg"}

IsUnaryExpr(expr) ==
    IF IsVar(expr) THEN 
        FALSE
    ELSE
        /\  "operator" \in DOMAIN expr
        /\  "right" \in DOMAIN expr
        /\  expr["operator"] \in UnaryOpSet

    
IsExpression(var) ==
    \/ IsBinaryExpr(var)
    \/ IsUnaryExpr(var)

\* We have to delcare the recursive function before we can use it for mutual recursion
RECURSIVE ApplyBinaryExpr(_, _, _)
RECURSIVE ApplyUnaryExpr(_, _, _)

EvalExpr(t, workgroupId, expr) ==
    IF IsIndex(expr) THEN
        expr.realIndex
    ELSE IF IsBinaryExpr(expr) = TRUE THEN
        ApplyBinaryExpr(t, workgroupId, expr)
    ELSE IF IsUnaryExpr(expr) = TRUE THEN 
        ApplyUnaryExpr(t, workgroupId, expr)
    ELSE
        GetVal(workgroupId, Mangle(t, expr))
        \* GetVal(workgroupId, expr)
    

ApplyBinaryExpr(t, workgroupId, expr) ==
    LET lhsValue == EvalExpr(t, workgroupId, expr["left"])
        rhsValue == EvalExpr(t, workgroupId, expr["right"])
    IN
        IF expr["operator"] = "LessThan" THEN
            LessThan(lhsValue, rhsValue)
        ELSE IF expr["operator"] = "LessThanOrEqual" THEN
            LessThanOrEqual(lhsValue, rhsValue)
        ELSE IF expr["operator"] = "GreaterThan" THEN
            GreaterThan(lhsValue, rhsValue)
        ELSE IF expr["operator"] = "GreaterThanOrEqual" THEN
            GreaterThanOrEqual(lhsValue, rhsValue)
        ELSE IF expr["operator"] = "Equal" THEN
            Equal(lhsValue, rhsValue)
        ELSE IF expr["operator"] = "NotEqual" THEN
            NotEqual(lhsValue, rhsValue)
        ELSE IF expr["operator"] = "Plus" THEN
            Plus(lhsValue, rhsValue)
        ELSE IF expr["operator"] = "Minus" THEN
            Minus(lhsValue, rhsValue)
        ELSE IF expr["operator"] = "Multiply" THEN
            Multiply(lhsValue, rhsValue)
        ELSE IF expr["operator"] = "Indexing" THEN
            Indexing(lhsValue, rhsValue)
        ELSE
            FALSE

ApplyUnaryExpr(t, workgroupId, expr) == 
    /\  LET rhsValue == EvalExpr(t, workgroupId, expr["right"])
        IN
            /\  IF expr["operator"] = "Not" THEN
                    Not(rhsValue)
                ELSE IF expr["operator"] = "Neg" THEN
                    Neg(rhsValue)

                ELSE
                    FALSE

(* Thread Configuration *)
InstructionSet == {"Assert", "Assignment", "OpAtomicLoad", "OpAtomicStore", "OpAtomicIncrement" , "OpAtomicDecrement", "OpGroupAll", "OpGroupAny", "OpGroupNonUniformAll", "OpGroupNonUniformAllEqual",
"OpGroupNonUniformAny", "OpGroupNonUniformBroadcast", "OpAtomicCompareExchange" ,"OpAtomicExchange", "OpBranch", "OpBranchConditional", "OpSwitch", "OpControlBarrier", "OpLoopMerge",
"OpSelectionMerge", "OpLabel", "Terminate", "OpLogicalOr", "OpLogicalAnd", "OpLogicalEqual", "OpLogicalNotEqual", "OpLogicalNot", "OpShiftLeftLogical", "OpShiftRightLogical", "OpBitcast", "OpBitwiseOr", "OpBitwiseAnd",
"OpEqual", "OpNotEqual", "OpLess", "OpLessOrEqual", "OpGreater", "OpGreaterOrEqual",
"OpAdd", "OpAtomicAdd", "OpSub", "OpAtomicSub", "OpAtomicOr", "OpAtomicAnd", "OpMul", "OpMod"}
VariableScope == {"global", "shared", "local", "literal", "intermediate"}
ScopeOperand == {"workgroup", "subgroup", "tangle"}
MemoryOperationSet == {"OpAtomicLoad", "OpAtomicStore", "OpAtomicIncrement" , "OpAtomicDecrement",
"OpAtomicAdd" , "OpAtomicSub", "OpAtomicCompareExchange" ,"OpAtomicExchange", "OpAtomicOr", "OpAtomicAnd"}

BranchInstructionSet == {"OpBranch", "OpBranchConditional", "OpSwitch"}

IsMemoryOperation(inst) == 
    inst \in MemoryOperationSet

\* SIMT-Step subgroup collectives (always collective in every model).
SubgroupInstructionSet == {"OpGroupAll", "OpGroupAny", "OpGroupNonUniformAll", "OpGroupNonUniformAllEqual", "OpGroupNonUniformAny", "OpGroupNonUniformBroadcast"}

\* Per Table 1 in the paper: map the model label to its collective set.
CollectiveInstructionSet ==
    LET base == SubgroupInstructionSet IN
        CASE Synchronization = "CM" -> base \cup MemoryOperationSet \cup BranchInstructionSet \cup {"OpLabel"}
             [] Synchronization = "SM" -> base \cup BranchInstructionSet \cup {"OpLabel"}
             [] Synchronization = "SCF" -> base \cup BranchInstructionSet \cup {"OpLabel"}
             [] Synchronization = "SSO" -> base
             [] OTHER -> base

\* Only SM maps memory ops to the Arrive/Execute semantics (§4.2).
SynchronousInstructionSet ==
    CASE Synchronization = "CM" -> {}
         [] Synchronization = "SM" -> MemoryOperationSet
         [] Synchronization = "SCF" -> {}
         [] Synchronization = "SSO" -> {}
         [] OTHER -> {}

IndependentInstructionSet == InstructionSet \ (CollectiveInstructionSet \cup SynchronousInstructionSet)

IsCollectiveInstruction(instr) == instr \in CollectiveInstructionSet

IsSynchronousInstruction(instr) == instr \in SynchronousInstructionSet

IsIndependentInstruction(instr) == instr \in IndependentInstructionSet

\* order matters so we use sequence instead of set
\* currentThreadSet is the set of threads that are currently executing the block
\* executeSet is the set of blocks that have been executed by the threads
\* currentThreadSet != {} => executeSet != {}
\* executeSet = {} => currentThreadSet = {}
DynamicNode(sis, currentThreadSet, executeSet, notExecuteSet, unknownSet, labelIdx, id, mergeStack, children) ==
    [
        sis |-> sis,
        currentThreadSet |-> currentThreadSet,
        executeSet |-> executeSet,
        notExecuteSet |-> notExecuteSet,
        unknownSet |-> unknownSet,
        labelIdx |-> labelIdx,
        id |-> id,
        mergeStack |-> mergeStack,
        children |-> children
    ]


(* Program *)



EntryLabel == Min({idx \in 1..Len(ThreadInstructions[1]) : ThreadInstructions[1][idx] = "OpLabel"})
MaxInstructionIdx == Len(ThreadInstructions[1])

\* SIS keeps the Arrive/Execute flag for each workgroup, subgroup, and instruction (§4.2).
EmptySIS == [wg \in 1..NumWorkGroups |-> [sg \in 1..NumSubgroupsPerWorkgroup |-> [pc \in 1..MaxInstructionIdx |-> FALSE]]]

SetSISFlag(db, wgid, sg, pc, val) == [db EXCEPT !.sis[wgid][sg][pc] = val]

SubgroupIndex(tid) == SubgroupId(tid) + 1

ReplaceDB(DBSet, oldDB, newDB) == (DBSet \ {oldDB}) \union {newDB}

\* Helper: update the SIS flag for a particular workgroup/subgroup/pc entry.
SetSISInDB(DBSet, oldDB, wgid, sg, pc, val) == ReplaceDB(DBSet, oldDB, SetSISFlag(oldDB, wgid, sg, pc, val))

(* CFG *)


\* Synchronization == "Collective"
INSTANCE ProgramConf



(* Inovactions within a tangle are required to execute tangled instruction concurrently, examples or opGroup operations and opControlBarrier  *)
TangledInstructionSet == {"OpControlBarrier, OpGroupAll", "OpGroupAny", "OpGroupNonUniformAll", "OpGroupNonUniformAllEqual", "OpGroupNonUniformAny", "OpGroupNonUniformBroadcast"}
MergedInstructionSet == {"OpLoopMerge", "OpSelectionMerge"}
BlockTerminationInstructionSet == {"OpBranch", "OpBranchConditional", "OpSwitch", "Terminate"}
ConstructTypeSet == {"Selection", "Loop", "Switch", "Continue", "Case"}
\* Tangle: 
Tangle(ts) == 
    [threads |-> ts]

OrderSet(set) == CHOOSE seq \in [1..Cardinality(set) -> set]: Range(seq) = set

\* make non-order-sensitive sequence becomes enumerable
SeqToSet(seq) == { seq[i]: i \in 1..Len(seq) }

\* update the sequence of sets
newSeqOfSets(seq, idx, newSet) == [seq EXCEPT ![idx] = newSet]

\* BoundedSeq: return a set of all sequences of length at most n, this helps to make the sequence enumerable
BoundedSeq(S, N) == UNION { [1..n -> S]: n \in 0..N}


\* helper function to extract the OpLabel field from the block
ExtractOpLabelIdxSet(blocks) ==
    {blocks[blockIdx].opLabelIdx : blockIdx \in 1..Len(blocks)}

        

\* mergeBlock is the current merge block,
\* return header block for current merge block
FindHeaderBlock(blocks, mBlock) == 
    CHOOSE block \in SeqToSet(blocks) : mBlock.opLabelIdx = block.mergeBlock

(* Helper function to find the block that starts with the given index to OpLabel *)
FindBlockbyOpLabelIdx(blocks, index) == 
    CHOOSE block \in SeqToSet(blocks): block.opLabelIdx = index

(* Helper function to find the block that ends with the given index to termination instruction *)
FindBlockByTerminationIns(blocks, index) == 
    CHOOSE block \in SeqToSet(blocks): block.terminatedInstrIdx = index

GetSwitchTargets(block) ==
    LET
        switchInstrIdx == block.terminatedInstrIdx
        switchTargets == {GetVal(-1, ThreadArguments[1][switchInstrIdx][i]) : i \in 2..Len(ThreadArguments[1][switchInstrIdx])}
    IN
        switchTargets


\* function to determine if the merge instruction contains the given label as operand
\* mergeInsIdx is the pc of the merge instruction
\* opLabel is the value(label) that we are looking for
MergeInstContainsLabel(mergeInsIdx, opLabel) == 
   IF ThreadInstructions[1][mergeInsIdx] = "OpLoopMerge" THEN
        ThreadArguments[1][mergeInsIdx][1].name = opLabel \/ ThreadArguments[1][mergeInsIdx][2].name = opLabel
    ELSE IF ThreadInstructions[1][mergeInsIdx] = "OpSelectionMerge" THEN
        ThreadArguments[1][mergeInsIdx][1].name = opLabel
    ELSE
        FALSE

MergeInstContainsLabelIdx(mergeInsIdx, opLabelIdx) == 
   IF ThreadInstructions[1][mergeInsIdx] = "OpLoopMerge" THEN
        GetVal(-1, ThreadArguments[1][mergeInsIdx][1]) = opLabelIdx 
        \/ GetVal(-1, ThreadArguments[1][mergeInsIdx][2]) = opLabelIdx
    ELSE IF ThreadInstructions[1][mergeInsIdx] = "OpSelectionMerge" THEN
        GetVal(-1, ThreadArguments[1][mergeInsIdx][1]) = opLabelIdx
    ELSE
        FALSE


IsTerminationInstruction(instr) ==
    instr \in BlockTerminationInstructionSet

IsBranchInstruction(instr) ==
    instr \in BranchInstructionSet

IsMergedInstruction(instr) ==
    instr \in MergedInstructionSet

IsOpLabel(instr) ==
    instr = "OpLabel"

IsMergeBlock(blockIdx) ==
    /\ \E construct \in ControlFlowConstructs : construct.mergeBlock = blockIdx

IsConstructHeaderBlock(blockIdx) ==
    /\ \E construct \in ControlFlowConstructs : construct.headerBlock = blockIdx

IsHeaderBlock(block) ==
    block.mergeBlock # -1


IsLoopHeaderBlock(block) ==
    /\ IsHeaderBlock(block)
    /\ block.constructType = "Loop"

IsContinueBlock(blockIdx) == 
    /\ \E construct \in ControlFlowConstructs : construct.constructType = "Loop" /\ construct.continueTarget = blockIdx

IsContinueBlockOf(currentBlock, headerBlock) ==
    /\ IsLoopHeaderBlock(headerBlock)
    /\ IsMergeBlock(currentBlock.opLabelIdx)
    /\ headerBlock.continueBlock = currentBlock.opLabelIdx

IsExitBlock(block) ==
  IsTerminationInstruction(block.terminatedInstrIdx)
(* Helper function to find the block that contains the given index *)
FindCurrentBlock(blocks, index) == 
    CHOOSE block \in SeqToSet(blocks): block.opLabelIdx <= index /\ block.terminatedInstrIdx >= index

\* lookback function that helps to determine if the current block is a merge block
\* startIdx is the pc of the instruction(OpLabel) that starts the current block
DetermineBlockType(startIdx) ==
    IF \E instIdx \in 1..(startIdx-1):
        IsMergedInstruction(ThreadInstructions[1][instIdx]) 
        /\ MergeInstContainsLabelIdx(instIdx, startIdx)
    THEN 
        TRUE
    ELSE 
        FALSE


\* it is only possible for a thread to be in one DB at a time
CurrentDynamicNode(wgid, tid) ==
    CHOOSE DB \in DynamicNodeSet : tid \in DB.currentThreadSet[wgid]

FindDB(labelIdx) ==
    CHOOSE DB \in DynamicNodeSet : DB.labelIdx = labelIdx

IsMergeBlockOfLoop(blockIdx) ==
    /\ \E construct \in ControlFlowConstructs : construct.constructType = "Loop" /\ construct.mergeBlock = blockIdx

GetConstructOfLoop(mergeBlockIdx) ==
    CHOOSE construct \in ControlFlowConstructs : construct.constructType = "Loop" /\ construct.mergeBlock = mergeBlockIdx

BlocksInSameLoopConstruct(headerIdx, mergeIdx) ==
    CHOOSE  construct \in ControlFlowConstructs : construct.constructType = "Loop" /\ construct.headerBlock = headerIdx /\ construct.mergeBlock = mergeIdx

IsBlockWithinLoop(blockIdx) ==
    LET matchingConstructs == {c \in ControlFlowConstructs : blockIdx \in c.blocks}
    IN
        /\ matchingConstructs # {}
        /\ \E c \in matchingConstructs : c.constructType = "Loop" 

\* This function is useful because it helps to determine the blocks that are being affeced by the change of tangle of current block
BlocksInSameConstruct(mergeIdx) ==
    CHOOSE  construct \in ControlFlowConstructs : construct.mergeBlock = mergeIdx


UniqueBlockId(blockIdx, counter) ==
    [blockIdx |-> blockIdx,
     counter |-> counter]
    
    
Iteration(blockIdx, iter) == 
    [blockIdx |-> blockIdx,
     iter |-> iter]

FindIteration(blockIdx, iterationsVec, tid) ==
    IF Len(iterationsVec) = 0
    THEN
        Iteration(blockIdx, 0)
    ELSE IF iterationsVec[Len(iterationsVec)].blockIdx = blockIdx
    THEN
        iterationsVec[Len(iterationsVec)]
    ELSE
        Iteration(blockIdx, 0)

SameMergeStack(left, mergeBlock) ==
    IF Len(mergeBlock) = 0 THEN 
        TRUE
    ELSE IF Len(left) >= Len(mergeBlock) THEN
        SubSeq(left, 1, Len(mergeBlock)) = mergeBlock
    ELSE 
        FALSE


SameSwitchHeader(targetDB, currentDB) ==
    /\ \E DB \in DynamicNodeSet : 
        \* find DB that is the switch header block
        /\  \E construct \in ControlFlowConstructs : 
                /\  construct.constructType = "Switch" 
                /\  construct.headerBlock = DB.labelIdx 
        \*  and contains the target DB as its child
        /\  \E child \in DB.children : child.blockIdx = targetDB.labelIdx /\ child.counter = targetDB.id
        \*  and contains the current DB as its child
        /\  \E child \in DB.children : child.blockIdx = currentDB.labelIdx /\ child.counter = currentDB.id

FindSwitchHeader(block) ==
    CHOOSE DB \in DynamicNodeSet : 
        \E construct \in ControlFlowConstructs : 
            /\  construct.constructType = "Switch" 
            /\  construct.headerBlock = DB.labelIdx 
            /\ construct.mergeBlock = DB.mergeStack[Len(DB.mergeStack)].blockIdx
SameIterationVector(left, right) ==
    /\ Len(left) = Len(right)
    /\ \A idx \in 1..Len(left):
        /\ left[idx].blockIdx = right[idx].blockIdx
        /\ left[idx].iter = right[idx].iter

CanMergeSameIterationVector(curr, remaining) ==
    \E idx \in 1..Len(remaining):
        SameIterationVector(curr, remaining[idx])



\* Independent control flow
BranchUpdate(wgid, t, pc, opLabelIdxSet, chosenBranchIdx, falseLabels) ==
    LET
        currentCounter == globalCounter
        currentBranchOptions == OrderSet(opLabelIdxSet)
        currentDB == CurrentDynamicNode(wgid, t)
        falseLabelIdxSet == falseLabels \ {chosenBranchIdx}  
        labelIdxSet == {DB.labelIdx : DB \in DynamicNodeSet}
        choosenBlock == FindBlockbyOpLabelIdx(Blocks, chosenBranchIdx)
        currentBlock == FindBlockbyOpLabelIdx(Blocks, currentDB.labelIdx)
        currentChildren == currentDB.children
        currentMergeStack == currentDB.mergeStack
        \* it determines if the current db has already created the dynamic block for branching
        childrenContainsAllBranchDB == \A i \in 1..Len(currentBranchOptions):
            \E  child \in currentChildren: child.blockIdx = currentBranchOptions[i]
        isHeaderBlock == IsHeaderBlock(currentBlock)
        isMergeBlock == IsMergeBlock(currentBlock.opLabelIdx)
        \* check if current header block already has a merge block
        mergeStackContainsCurrent == isHeaderBlock /\ Len(currentMergeStack) # 0 /\ currentMergeStack[Len(currentMergeStack)].blockIdx = currentBlock.mergeBlock
        updatedMergeStack == 
            IF mergeStackContainsCurrent \/ isHeaderBlock = FALSE THEN 
                currentMergeStack
            ELSE
                Push(currentMergeStack, UniqueBlockId(currentBlock.mergeBlock, currentCounter + 1))
        \* update the children if firstly reach the divergence
        \* otherwise keep as it is
        counterAfterMergeStack == 
            IF isHeaderBlock = FALSE  \/ mergeStackContainsCurrent THEN
                currentCounter
            ELSE
                currentCounter + 1
        updatedChildren == 
            IF childrenContainsAllBranchDB THEN
                currentChildren
            ELSE
                currentChildren \union 
                {
                    IF IsMergeBlock(currentBranchOptions[i]) /\ \E index \in DOMAIN updatedMergeStack: updatedMergeStack[index].blockIdx = currentBranchOptions[i]
                    THEN 
                        UniqueBlockId(currentBranchOptions[i], updatedMergeStack[(CHOOSE index \in DOMAIN updatedMergeStack: updatedMergeStack[index].blockIdx = currentBranchOptions[i])].counter)
                    \* treat switch construct specially
                    ELSE IF \E DB \in DynamicNodeSet: DB.labelIdx = currentBranchOptions[i] /\ SameSwitchHeader(DB, currentDB) THEN
                        UniqueBlockId(currentBranchOptions[i], (CHOOSE DB \in DynamicNodeSet: DB.labelIdx = currentBranchOptions[i] /\ SameSwitchHeader(DB, currentDB)).id)
                    ELSE
                        UniqueBlockId(currentBranchOptions[i], counterAfterMergeStack + i)
                    : i \in 1..Len(currentBranchOptions)
                }
        updatedCounter == currentCounter + Cardinality(updatedChildren) - Cardinality(currentChildren) + Len(updatedMergeStack) - Len(currentMergeStack)
        
        mergeBlock == currentBlock.mergeBlock
        \* exsiting dynamic blocks for false labels
        existingFalseLabelIdxSet == {
            falselabelIdx \in falseLabelIdxSet: 
                \E DB \in DynamicNodeSet: DB.labelIdx = falselabelIdx /\ \E child \in updatedChildren: child.blockIdx = DB.labelIdx /\ child.counter = DB.id
                
        }
        \* we want to update the blocks in construct if choosen block is merge block
        constructUpdate == 
            IF IsMergeBlock(chosenBranchIdx) THEN
                LET construct == BlocksInSameConstruct(chosenBranchIdx)
                IN
                    construct.blocks \union {construct.continueTarget}
            ELSE
                {}
        \* this is set of all threads that are not terminated and still in the current construct
        unionSet == 
            [wg \in 1..NumWorkGroups |-> currentDB.currentThreadSet[wg] \union currentDB.executeSet[wg] \union currentDB.notExecuteSet[wg] \union currentDB.unknownSet[wg]]
    IN
        << updatedCounter, 
        \* update the existing dynamic blocks
        {
            \* if the constructUpdate is not empty, it means we are exiting a construct, all the dynamic blocks in that construct should be properly updated
            \* remove current thread from all set as it is not partcipating in the construct anymore
            IF DB.labelIdx \in constructUpdate /\ SameMergeStack(DB.mergeStack, currentMergeStack) THEN
                DynamicNode(DB.sis,
                    [DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \ {t}],
                    [ DB.executeSet EXCEPT ![wgid] = DB.executeSet[wgid] \ {t}],
                    [ DB.notExecuteSet EXCEPT ![wgid] = DB.notExecuteSet[wgid] \ {t}],
                    [ DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ {t}],
                    DB.labelIdx,
                    DB.id,
                    IF DB.labelIdx = currentDB.labelIdx /\ DB.id = currentDB.id THEN 
                        updatedMergeStack
                    ELSE 
                        DB.mergeStack
                    ,
                    IF DB.labelIdx = currentDB.labelIdx /\ DB.id = currentDB.id THEN
                        updatedChildren
                    ELSE
                    DB.children)
            \* if encounter current dynamic block
            ELSE IF DB.labelIdx = currentDB.labelIdx /\ DB.id = currentDB.id THEN
                DynamicNode(DB.sis,
                    [DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \ {t}],
                    DB.executeSet,
                    DB.notExecuteSet,
                    DB.unknownSet,
                    DB.labelIdx,
                    DB.id,
                    updatedMergeStack,
                    updatedChildren)

            \* if encounter choosen dynamic block
            \* whether its in current DB's children or on the top of the merge stack, we update it
            ELSE IF DB.labelIdx = chosenBranchIdx 
                    /\ \E child \in updatedChildren: child.blockIdx = DB.labelIdx /\ child.counter = DB.id
            THEN
                DynamicNode(DB.sis,
                    [DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \union {t}],
                    [DB.executeSet EXCEPT ![wgid] = DB.executeSet[wgid] \union {t}],
                    DB.notExecuteSet,
                    [DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ {t}],
                    DB.labelIdx,
                    DB.id,
                    DB.mergeStack,
                    DB.children)
            \* Encounter the block that is not choosen by the branch instruction
            \* we don't update the existing set for merge block as threads will eventually reach there unless they terminate early
            ELSE IF DB.labelIdx \in falseLabelIdxSet
                /\ IsMergeBlock(DB.labelIdx) = FALSE
                /\ \E child \in updatedChildren: child.blockIdx = DB.labelIdx /\ child.counter = DB.id
           
            THEN
                DynamicNode(DB.sis,
                    DB.currentThreadSet,
                    DB.executeSet,
                    [DB.notExecuteSet EXCEPT ![wgid] = DB.notExecuteSet[wgid] \union {t}],
                    [DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ {t}],
                    DB.labelIdx,
                    DB.id,
                    DB.mergeStack,
                    DB.children)
            
            ELSE
                DB
            : DB \in DynamicNodeSet
        }
        \* union with the new true branch DB if does not exist
        \union
        (
            IF \E DB \in DynamicNodeSet: 
                DB.labelIdx = chosenBranchIdx /\ \E child \in updatedChildren: child.blockIdx = DB.labelIdx /\ child.counter = DB.id
            THEN 
                {} 
            ELSE
                IF chosenBranchIdx \in constructUpdate THEN
                    {DynamicNode(EmptySIS,
                                [wg \in 1..NumWorkGroups |-> {}],
                                [wg \in 1..NumWorkGroups |-> {}],
                                [wg \in 1..NumWorkGroups |-> {}],
                                [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN unionSet[wgid] \ {t}  ELSE unionSet[wg]],
                                chosenBranchIdx,
                                LET child == CHOOSE child \in updatedChildren: child.blockIdx = chosenBranchIdx
                                IN
                                    child.counter,
                                updatedMergeStack,
                                {})
                    }
                \* if the choosen block is a merge block , we need to pop the merge stack of current DB.
                ELSE IF IsMergeBlock(chosenBranchIdx) THEN 
                    {
                        DynamicNode(EmptySIS,
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN {t} ELSE {}],
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN {t} ELSE {}],
                                    [wg \in 1..NumWorkGroups |-> {}],
                                    \* [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN ThreadsWithinWorkGroupNonTerminated(wgid-1) \ {t}  ELSE ThreadsWithinWorkGroupNonTerminated(wg-1)],
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN unionSet[wgid] \ {t}  ELSE unionSet[wg]],
                                    chosenBranchIdx,
                                    LET child == CHOOSE child \in updatedChildren: child.blockIdx = chosenBranchIdx
                                    IN
                                        child.counter,
                                    PopUntilBlock(updatedMergeStack, chosenBranchIdx),
                                    {}
                                    )
                    }
                ELSE
                    {
                        DynamicNode(EmptySIS,
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN {t} ELSE {}],
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN {t} ELSE {}],
                                    \* [wg \in 1..NumWorkGroups |-> DB.notExecuteSet[wg]],
                                    [wg \in 1..NumWorkGroups |-> {}],
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN unionSet[wgid] \ {t}  ELSE unionSet[wg]],
                                    chosenBranchIdx,
                                    LET child == CHOOSE child \in updatedChildren: child.blockIdx = chosenBranchIdx
                                    IN
                                        child.counter,
                                    updatedMergeStack,
                                    {})
                    }
        )
        \* union with the new false branch DB if does not exist
        \union
        (
        {   
            \* thread is exiting the construct, we also need to create a new dynamic block for false label and remove current thread from all sets of new block.
            IF falselabelIdx \in constructUpdate THEN 
                DynamicNode(EmptySIS,
                            [wg \in 1..NumWorkGroups |-> {}],
                            [wg \in 1..NumWorkGroups |-> {}],
                            [wg \in 1..NumWorkGroups |-> {}],
                            [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN unionSet[wgid] \ {t}  ELSE unionSet[wg]],
                            falselabelIdx,
                            LET child == CHOOSE child \in updatedChildren: child.blockIdx = falselabelIdx
                            IN
                                child.counter,
                            updatedMergeStack,
                            {})
            \* if new false branch is merge block, we need to pop the merge stack of current DB.
            ELSE IF IsMergeBlock(falselabelIdx) = TRUE THEN 
                DynamicNode(EmptySIS,
                            [wg \in 1..NumWorkGroups |-> {}], \* currently no thread is executing the false block
                            [wg \in 1..NumWorkGroups |-> {}], \* currently no thread has executed the false block
                            \* We don't know if the threads executed in precedessor DB will execute the block or not
                            [wg \in 1..NumWorkGroups |-> {}],
                            \* we don't know if the threads executed in precedessor DB will execute the block or not
                            \* [wg \in 1..NumWorkGroups |->  ThreadsWithinWorkGroupNonTerminated(wg-1)],
                            [wg \in 1..NumWorkGroups |-> unionSet[wg]],
                            falselabelIdx,
                            LET child == CHOOSE child \in updatedChildren: child.blockIdx = falselabelIdx
                            IN
                                child.counter,
                            PopUntilBlock(updatedMergeStack, falselabelIdx),
                            {})
            ELSE 
                DynamicNode(EmptySIS,
                            [wg \in 1..NumWorkGroups |-> {}], \* currently no thread is executing the false block
                            [wg \in 1..NumWorkGroups |-> {}], \* currently no thread has executed the false block
                            \* current thread is not executed in the false block, but we don't know if the threads executed in precedessor DB will execute the block or not
                            [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN {t} ELSE {}],
                            \* we don't know if the threads executed in precedessor DB will execute the block or not
                            \* [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN ThreadsWithinWorkGroupNonTerminated(wgid-1) \ {t}  ELSE ThreadsWithinWorkGroupNonTerminated(wg-1)],
                            [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN unionSet[wgid] \ {t}  ELSE unionSet[wg]],
                            falselabelIdx,
                            LET child == CHOOSE child \in updatedChildren: child.blockIdx = falselabelIdx
                            IN
                                child.counter,
                            updatedMergeStack,
                            {})
            : falselabelIdx \in (falseLabelIdxSet \ existingFalseLabelIdxSet)
        }
        )>>


\* Collective control flow
BranchConditionalUpdateSubgroup(wgid, active_subgroup_threads, pc, opLabelIdxSet, trueThreads, falseThreads, trueLabelVal, falseLabelVal) ==
    LET
        currentCounter == globalCounter
        currentBranchOptions == OrderSet(opLabelIdxSet)
        \* Use any thread from the subgroup to get current dynamic block (they should all be in the same block)
        representative_thread == CHOOSE t \in active_subgroup_threads: TRUE
        currentDB == CurrentDynamicNode(wgid, representative_thread)
        falseLabelIdxSet == IF falseThreads = {} THEN 
            {}
        ELSE
            opLabelIdxSet \ {trueLabelVal, falseLabelVal}  
        labelIdxSet == {DB.labelIdx : DB \in DynamicNodeSet}
        choosenTrueBlock == FindBlockbyOpLabelIdx(Blocks, trueLabelVal)
        choosenFalseBlock == IF falseThreads = {} THEN
                [
                    opLabelIdx |-> -1,
                    terminatedInstrIdx |-> -1,
                    tangle |-> <<{}>>,
                    merge |-> FALSE,
                    initialized |-> <<TRUE>>,
                    constructType |-> "Selection",
                    mergeBlock |-> -1,
                    continueBlock |-> -1,
                    defaultBlock |-> -1,
                    caseBlocks |-> <<>>
                ]
            ELSE
                FindBlockbyOpLabelIdx(Blocks, falseLabelVal)
        currentBlock == FindBlockbyOpLabelIdx(Blocks, currentDB.labelIdx)
        currentChildren == currentDB.children
        currentMergeStack == currentDB.mergeStack
        \* it determines if the current db has already created the dynamic block for branching
        childrenContainsAllBranchDB == \A i \in 1..Len(currentBranchOptions):
            \E  child \in currentChildren: child.blockIdx = currentBranchOptions[i]
        isHeaderBlock == IsHeaderBlock(currentBlock)
        isMergeBlock == IsMergeBlock(currentBlock.opLabelIdx)
        \* check if current header block already has a merge block
        mergeStackContainsCurrent == isHeaderBlock /\ Len(currentMergeStack) # 0 /\ currentMergeStack[Len(currentMergeStack)].blockIdx = currentBlock.mergeBlock
        updatedMergeStack == 
            IF mergeStackContainsCurrent \/ isHeaderBlock = FALSE THEN 
                currentMergeStack
            ELSE
                Push(currentMergeStack, UniqueBlockId(currentBlock.mergeBlock, currentCounter + 1))
        \* update the children if firstly reach the divergence
        counterAfterMergeStack == 
            IF isHeaderBlock = FALSE  \/ mergeStackContainsCurrent THEN
                currentCounter
            ELSE
                currentCounter + 1
        updatedChildren == 
            IF childrenContainsAllBranchDB THEN
                currentChildren
            ELSE
                currentChildren \union 
                {
                    IF IsMergeBlock(currentBranchOptions[i]) /\ \E index \in DOMAIN updatedMergeStack: updatedMergeStack[index].blockIdx = currentBranchOptions[i]
                    THEN 
                        UniqueBlockId(currentBranchOptions[i], updatedMergeStack[(CHOOSE index \in DOMAIN updatedMergeStack: updatedMergeStack[index].blockIdx = currentBranchOptions[i])].counter)
                    \* treat switch construct specially
                    ELSE IF \E DB \in DynamicNodeSet: DB.labelIdx = currentBranchOptions[i] /\ SameSwitchHeader(DB, currentDB) THEN
                        UniqueBlockId(currentBranchOptions[i], (CHOOSE DB \in DynamicNodeSet: DB.labelIdx = currentBranchOptions[i] /\ SameSwitchHeader(DB, currentDB)).id)
                    ELSE
                        UniqueBlockId(currentBranchOptions[i], counterAfterMergeStack + i)
                    : i \in 1..Len(currentBranchOptions)
                }
        \* We only update the merge stack if the current block is a header block and if firstly reach the divergence
        \* globalCounter is only updated when we firstly reach the divergence
        updatedCounter == currentCounter + Cardinality(updatedChildren) - Cardinality(currentChildren) + Len(updatedMergeStack) - Len(currentMergeStack)
        
        mergeBlock == currentBlock.mergeBlock
        \* existing dynamic blocks for false labels (not chosen by any thread)
        existingFalseLabelIdxSet == {
            falselabelIdx \in falseLabelIdxSet: 
                \E DB \in DynamicNodeSet: DB.labelIdx = falselabelIdx /\ \E child \in updatedChildren: child.blockIdx = DB.labelIdx /\ child.counter = DB.id
        }
        \* we want to update the blocks in construct if choosen block is merge block
        constructUpdateTrue == 
            IF IsMergeBlock(choosenTrueBlock.opLabelIdx) THEN
                LET construct == BlocksInSameConstruct(choosenTrueBlock.opLabelIdx)
                IN
                    construct.blocks \union {construct.continueTarget}
            ELSE
                {}
        constructUpdateFalse == 
            IF IsMergeBlock(choosenFalseBlock.opLabelIdx) THEN
                LET construct == BlocksInSameConstruct(choosenFalseBlock.opLabelIdx)
                IN
                    construct.blocks \union {construct.continueTarget}
            ELSE
                {}
        \* this is set of all threads that are not terminated and still in the current construct
        unionSet == 
            [wg \in 1..NumWorkGroups |-> currentDB.currentThreadSet[wg] \union currentDB.executeSet[wg] \union currentDB.notExecuteSet[wg] \union currentDB.unknownSet[wg]]
    IN
        << updatedCounter, 
        \* update the existing dynamic blocks
        {
            \* if the constructUpdate is not empty for true branch, remove true threads from construct blocks
            IF DB.labelIdx \in constructUpdateTrue /\ SameMergeStack(DB.mergeStack, currentMergeStack) THEN
                DynamicNode(DB.sis,
                    [DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \ trueThreads],
                    [ DB.executeSet EXCEPT ![wgid] = DB.executeSet[wgid] \ trueThreads],
                    [ DB.notExecuteSet EXCEPT ![wgid] = DB.notExecuteSet[wgid] \ trueThreads],
                    [ DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ trueThreads],
                    DB.labelIdx,
                    DB.id,
                    IF DB.labelIdx = currentDB.labelIdx /\ DB.id = currentDB.id THEN 
                        updatedMergeStack
                    ELSE 
                        DB.mergeStack,
                    IF DB.labelIdx = currentDB.labelIdx /\ DB.id = currentDB.id THEN
                        updatedChildren
                    ELSE
                        DB.children)
            \* if the constructUpdate is not empty for false branch, remove false threads from construct blocks
            ELSE IF DB.labelIdx \in constructUpdateFalse /\ SameMergeStack(DB.mergeStack, currentMergeStack) THEN
                DynamicNode(DB.sis,
                    [DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \ falseThreads],
                    [ DB.executeSet EXCEPT ![wgid] = DB.executeSet[wgid] \ falseThreads],
                    [ DB.notExecuteSet EXCEPT ![wgid] = DB.notExecuteSet[wgid] \ falseThreads],
                    [ DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ falseThreads],
                    DB.labelIdx,
                    DB.id,
                    IF DB.labelIdx = currentDB.labelIdx /\ DB.id = currentDB.id THEN 
                        updatedMergeStack
                    ELSE 
                        DB.mergeStack,
                    IF DB.labelIdx = currentDB.labelIdx /\ DB.id = currentDB.id THEN
                        updatedChildren
                    ELSE
                        DB.children)
            \* if encounter current dynamic block, remove all active threads
            ELSE IF DB.labelIdx = currentDB.labelIdx /\ DB.id = currentDB.id THEN
                DynamicNode(DB.sis,
                    [DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \ active_subgroup_threads],
                    [DB.executeSet EXCEPT ![wgid] = DB.executeSet[wgid] \ active_subgroup_threads],
                    [DB.notExecuteSet EXCEPT ![wgid] = DB.notExecuteSet[wgid] \ active_subgroup_threads],
                    [DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ active_subgroup_threads],
                    DB.labelIdx,
                    DB.id,
                    updatedMergeStack,
                    updatedChildren)

            \* if encounter true branch dynamic block, add true threads
            ELSE IF DB.labelIdx = trueLabelVal 
                    /\ \E child \in updatedChildren: child.blockIdx = DB.labelIdx /\ child.counter = DB.id
            THEN
                IF IsMergeBlock(trueLabelVal) THEN
                    DynamicNode(DB.sis,
                        [DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \union trueThreads],
                        [DB.executeSet EXCEPT ![wgid] = DB.executeSet[wgid] \union trueThreads],
                        DB.notExecuteSet,
                        [DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ trueThreads],
                        DB.labelIdx,
                        DB.id,
                        DB.mergeStack,
                        DB.children)
                ELSE
                    DynamicNode(DB.sis,
                        [DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \union trueThreads],
                        [DB.executeSet EXCEPT ![wgid] = DB.executeSet[wgid] \union trueThreads],
                        [DB.notExecuteSet EXCEPT ![wgid] = DB.notExecuteSet[wgid] \union falseThreads],
                        [DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ active_subgroup_threads],
                        DB.labelIdx,
                        DB.id,
                        DB.mergeStack,
                        DB.children)
                    
            \* if encounter false branch dynamic block, add false threads
            ELSE IF DB.labelIdx = falseLabelVal 
                    /\ \E child \in updatedChildren: child.blockIdx = DB.labelIdx /\ child.counter = DB.id
            THEN
                IF IsMergeBlock(falseLabelVal) THEN
                    DynamicNode(DB.sis,
                        [DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \union falseThreads],
                        [DB.executeSet EXCEPT ![wgid] = DB.executeSet[wgid] \union falseThreads],
                        DB.notExecuteSet,
                        [DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ falseThreads],
                        DB.labelIdx,
                        DB.id,
                        DB.mergeStack,
                        DB.children)
                ELSE
                    DynamicNode(DB.sis,
                        [DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \union falseThreads],
                        [DB.executeSet EXCEPT ![wgid] = DB.executeSet[wgid] \union falseThreads],
                        [DB.notExecuteSet EXCEPT ![wgid] = DB.notExecuteSet[wgid] \union trueThreads],
                        [DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ active_subgroup_threads],
                        DB.labelIdx,
                        DB.id,
                        DB.mergeStack,
                        DB.children)
            
            ELSE 
                DB
            : DB \in DynamicNodeSet
        }
        \union
        \* create new true branch dynamic block if it doesn't exist
        (
            IF \E DB \in DynamicNodeSet: 
                DB.labelIdx = trueLabelVal /\ \E child \in updatedChildren: child.blockIdx = DB.labelIdx /\ child.counter = DB.id
            THEN 
                {} 
            ELSE
                \* Check if true branch is exiting a construct
                IF trueLabelVal \in constructUpdateTrue THEN
                    {DynamicNode(EmptySIS,
                                [wg \in 1..NumWorkGroups |-> {}],
                                [wg \in 1..NumWorkGroups |-> {}],
                                [wg \in 1..NumWorkGroups |-> {}],
                                [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN unionSet[wgid] \ active_subgroup_threads ELSE unionSet[wg]],
                                trueLabelVal,
                                LET child == CHOOSE child \in updatedChildren: child.blockIdx = trueLabelVal
                                IN
                                    child.counter,
                                updatedMergeStack,
                                {})
                    }
                \* Check if true branch is a merge block 
                ELSE IF IsMergeBlock(trueLabelVal) THEN 
                    {
                        DynamicNode(EmptySIS,
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN trueThreads ELSE {}],
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN trueThreads ELSE {}],
                                    [wg \in 1..NumWorkGroups |-> {}],
                                    \* [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN unionSet[wgid] \ active_subgroup_threads ELSE unionSet[wg]],
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN unionSet[wgid] \ trueThreads ELSE unionSet[wg]],
                                    trueLabelVal,
                                    LET child == CHOOSE child \in updatedChildren: child.blockIdx = trueLabelVal
                                    IN
                                        child.counter,
                                    PopUntilBlock(updatedMergeStack, trueLabelVal),
                                    {}
                                    )
                    }
                \* Default case for regular blocks
                ELSE
                    {
                        DynamicNode(EmptySIS,
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN trueThreads ELSE {}],
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN trueThreads ELSE {}],
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN falseThreads ELSE {}],
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN unionSet[wgid] \ active_subgroup_threads ELSE unionSet[wg]],
                        \* [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN unionSet[wgid] \ trueThreads ELSE unionSet[wg]],
                                    trueLabelVal,
                                    LET child == CHOOSE child \in updatedChildren: child.blockIdx = trueLabelVal
                                    IN
                                        child.counter,
                                    updatedMergeStack,
                                    {})
                    }
        )
        \union
        \* create new false branch dynamic block if it doesn't exist  
        (
            IF \E DB \in DynamicNodeSet: 
                falseLabelVal = -1 \/ (DB.labelIdx = falseLabelVal /\ \E child \in updatedChildren: child.blockIdx = DB.labelIdx /\ child.counter = DB.id)
            THEN 
                {} 
            ELSE
                \* Check if false branch is exiting a construct
                IF falseLabelVal \in constructUpdateFalse THEN
                    {DynamicNode(EmptySIS,
                                [wg \in 1..NumWorkGroups |-> {}],
                                [wg \in 1..NumWorkGroups |-> {}],
                                [wg \in 1..NumWorkGroups |-> {}],
                                \* [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN unionSet[wgid] \ active_subgroup_threads ELSE unionSet[wg]],
                                [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN unionSet[wgid] \ falseThreads ELSE unionSet[wg]],
                                falseLabelVal,
                                LET child == CHOOSE child \in updatedChildren: child.blockIdx = falseLabelVal
                                IN
                                    child.counter,
                                updatedMergeStack,
                                {})
                    }
                \* Check if false branch is a merge block 
                ELSE IF IsMergeBlock(falseLabelVal) THEN 
                    {
                        DynamicNode(EmptySIS,
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN falseThreads ELSE {}],
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN falseThreads ELSE {}],
                                    [wg \in 1..NumWorkGroups |-> {}],
                                    \* [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN unionSet[wgid] \ active_subgroup_threads ELSE unionSet[wg]],
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN unionSet[wgid] \ falseThreads ELSE unionSet[wg]],
                                    falseLabelVal,
                                    LET child == CHOOSE child \in updatedChildren: child.blockIdx = falseLabelVal
                                    IN
                                        child.counter,
                                    PopUntilBlock(updatedMergeStack, falseLabelVal),
                                    {}
                                    )
                    }
                \* Default case for regular blocks
                ELSE
                    {
                        DynamicNode(EmptySIS,
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN falseThreads ELSE {}],
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN falseThreads ELSE {}],
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN trueThreads ELSE {}],
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN unionSet[wgid] \ active_subgroup_threads ELSE unionSet[wg]],
                        \* [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN unionSet[wgid] \ falseThreads ELSE unionSet[wg]],
                                    falseLabelVal,
                                    LET child == CHOOSE child \in updatedChildren: child.blockIdx = falseLabelVal
                                    IN
                                        child.counter,
                                    updatedMergeStack,
                                    {})
                    }
        )
        >>

TerminateUpdate(wgid, t) ==
    {
        DynamicNode(DB.sis,
            [DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \ {t}],
            DB.executeSet,
            DB.notExecuteSet,
            [DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ {t}],
            DB.labelIdx,
            DB.id,
            DB.mergeStack,
            DB.children)
        : DB \in DynamicNodeSet
    }

(* Global Variables *)


InitGlobalCounter ==
    globalCounter = 0

InitProgram ==
    /\ InitDB
    /\ InitGPU
    /\ InitGlobalCounter

\* Invariant: Each thread belongs to exactly one DB
ThreadBelongsExactlyOne ==
    /\ \A t \in Threads:
        \E DB \in DynamicNodeSet:
            t \in DB.currentThreadSet[WorkGroupId(t) + 1]
    /\ \A t1, t2 \in Threads:
        IF WorkGroupId(t1) = WorkGroupId(t2) THEN 
            /\ \A DB1, DB2 \in DynamicNodeSet:
                (t1 \in DB1.currentThreadSet[WorkGroupId(t1) + 1] /\ t2 \in DB2.currentThreadSet[WorkGroupId(t2) + 1]) => DB1 = DB2
        ELSE
            TRUE

\* Invariant: Each dynamic execution graph has a unique block sequence
UniquelabelIdxuence ==
    \A DB1, DB2 \in DynamicNodeSet:
        DB1.labelIdx = DB2.labelIdx => DB1 = DB2
====
