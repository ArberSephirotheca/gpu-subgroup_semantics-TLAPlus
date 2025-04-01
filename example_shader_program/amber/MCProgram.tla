---- MODULE MCProgram ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets
\* LOCAL INSTANCE MCLayout
LOCAL INSTANCE TLC

VARIABLES globalVars, threadLocals, state, DynamicNodeSet, globalCounter

SubgroupSize == 1
WorkGroupSize == 1
NumWorkGroups == 2
NumSubgroups == 2
NumThreads == 2
Scheduler == "HSA"

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
"OpSelectionMerge", "OpLabel", "Terminate", "OpLogicalOr", "OpLogicalAnd", "OpLogicalEqual", "OpLogicalNotEqual", "OpLogicalNot", "OpShiftLeftLogical", "OpBitcast", "OpBitwiseOr", "OpBitwiseAnd",
"OpEqual", "OpNotEqual", "OpLess", "OpLessOrEqual", "OpGreater", "OpGreaterOrEqual",
"OpAdd", "OpAtomicAdd", "OpSub", "OpAtomicSub", "OpAtomicOr", "OpMul", "OpMod"}
VariableScope == {"global", "shared", "local", "literal", "intermediate"}
ScopeOperand == {"workgroup", "subgroup", "tangle"}
MemoryOperationSet == {"OpAtomicLoad", "OpAtomicStore", "OpAtomicIncrement" , "OpAtomicDecrement", "OpAtomicAdd" , "OpAtomicSub", "OpAtomicCompareExchange" ,"OpAtomicExchange"}

IsMemoryOperation(inst) == 
    inst \in MemoryOperationSet

\* order matters so we use sequence instead of set
\* currentThreadSet is the set of threads that are currently executing the block
\* executeSet is the set of blocks that have been executed by the threads
\* currentThreadSet != {} => executeSet != {}
\* executeSet = {} => currentThreadSet = {}
DynamicNode(currentThreadSet, executeSet, notExecuteSet, unknownSet, labelIdx, id, mergeStack, children) ==
    [
        currentThreadSet |-> currentThreadSet,
        executeSet |-> executeSet,
        notExecuteSet |-> notExecuteSet,
        unknownSet |-> unknownSet,
        labelIdx |-> labelIdx,
        id |-> id,
        mergeStack |-> mergeStack,
        children |-> children
    ]


ThreadInstructions ==  [t \in 1..NumThreads |-> <<
"Assignment",
"Assignment",
"Assignment",
"Assignment",
"Assignment",
"Assignment",
"OpLabel",
"Assignment",
"Assignment",
"Assignment",
"Assignment",
"Assignment",
"Assignment",
"Assignment",
"Assignment",
"Assignment",
"Assignment",
"OpAtomicStore",
"OpAtomicStore",
"OpAtomicStore",
"OpAtomicStore",
"OpAtomicStore",
"OpAtomicStore",
"OpAtomicStore",
"OpAtomicStore",
"OpMod",
"OpEqual",
"OpEqual",
"OpLogicalAnd",
"OpSelectionMerge",
"OpBranchConditional",
"OpLabel",
"OpAtomicStore",
"OpBranch",
"OpLabel",
"OpLoopMerge",
"OpBranch",
"OpLabel",
"OpBranchConditional",
"OpLabel",
"OpEqual",
"OpGroupNonUniformAny",
"OpSelectionMerge",
"OpBranchConditional",
"OpLabel",
"OpBranch",
"OpLabel",
"OpMod",
"OpAtomicStore",
"OpEqual",
"OpSelectionMerge",
"OpBranchConditional",
"OpLabel",
"OpSelectionMerge",
"OpSwitch",
"OpLabel",
"OpAtomicExchange",
"OpEqual",
"OpSelectionMerge",
"OpBranchConditional",
"OpLabel",
"OpAtomicStore",
"OpBranch",
"OpLabel",
"OpAdd",
"OpAtomicStore",
"OpBranch",
"OpLabel",
"OpBranch",
"OpLabel",
"OpAtomicStore",
"OpBranch",
"OpLabel",
"OpBranch",
"OpLabel",
"OpAdd",
"OpMod",
"OpAtomicStore",
"OpGroupNonUniformBroadcast",
"OpAtomicStore",
"OpBranch",
"OpLabel",
"OpBranch",
"OpLabel",
"OpBranch",
"OpLabel",
"OpMod",
"OpEqual",
"OpEqual",
"OpLogicalAnd",
"OpSelectionMerge",
"OpBranchConditional",
"OpLabel",
"OpAtomicStore",
"OpBranch",
"OpLabel",
"OpLoopMerge",
"OpBranch",
"OpLabel",
"OpBranchConditional",
"OpLabel",
"OpEqual",
"OpGroupNonUniformAny",
"OpSelectionMerge",
"OpBranchConditional",
"OpLabel",
"OpBranch",
"OpLabel",
"OpMod",
"OpAtomicStore",
"OpEqual",
"OpSelectionMerge",
"OpBranchConditional",
"OpLabel",
"OpSelectionMerge",
"OpSwitch",
"OpLabel",
"OpAtomicExchange",
"OpEqual",
"OpSelectionMerge",
"OpBranchConditional",
"OpLabel",
"OpAtomicStore",
"OpBranch",
"OpLabel",
"OpAdd",
"OpAtomicStore",
"OpBranch",
"OpLabel",
"OpBranch",
"OpLabel",
"OpAtomicStore",
"OpBranch",
"OpLabel",
"OpBranch",
"OpLabel",
"OpAdd",
"OpMod",
"OpAtomicStore",
"OpGroupNonUniformBroadcast",
"OpAtomicStore",
"OpBranch",
"OpLabel",
"OpBranch",
"OpLabel",
"OpBranch",
"OpLabel",
"OpControlBarrier",
"Terminate"
>>]

ThreadArguments == [t \in 1..NumThreads |-> <<
<<Var("local", "%gl_SubgroupSize", SubgroupSize, Index(-1))>>,
<<Var("local", "%gl_SubgroupID", SubgroupId(t), Index(-1))>>,
<<Var("local", "%gl_WorkGroupID", WorkGroupId(t), Index(-1))>>,
<<Var("local", "%gl_NumWorkGroups", NumWorkGroups, Index(-1))>>,
<<Var("local", "%gl_GlobalInvocationID", GlobalInvocationId(t), Index(-1))>>,
<<Var("local", "%gl_SubgroupInvocationID", SubgroupInvocationId(t), Index(-1))>>,
<<Var("global", "%5", 7, Index(-1))>>,
<<Var("local", "%subgroup_size", 0, Index(-1))>>,
<<Var("local", "%subgroup_id", 0, Index(-1))>>,
<<Var("local", "%workgroup_id", 0, Index(-1))>>,
<<Var("local", "%num_workgroups", 0, Index(-1))>>,
<<Var("local", "%gid_x", 0, Index(-1))>>,
<<Var("local", "%pc", 0, Index(-1))>>,
<<Var("local", "%round_robin", 0, Index(-1))>>,
<<Var("local", "%num_testing_subgroups", 0, Index(-1))>>,
<<Var("local", "%terminate", 0, Index(-1))>>,
<<Var("local", "%terminate_0", 0, Index(-1))>>,
<<Var("local", "%subgroup_size", "", Index(-1)), Var("local", "%gl_SubgroupSize", "", Index(-1))>>,
<<Var("local", "%subgroup_id", "", Index(-1)), Var("local", "%gl_SubgroupID", "", Index(-1))>>,
<<Var("local", "%workgroup_id", "", Index(-1)), Var("local", "%gl_WorkGroupID", "", Index(-1))>>,
<<Var("local", "%num_workgroups", "", Index(-1)), Var("local", "%gl_NumWorkGroups", "", Index(-1))>>,
<<Var("local", "%gid_x", "", Index(-1)), Var("local", "%gl_GlobalInvocationID", "", Index(-1))>>,
<<Var("local", "%pc", "", Index(-1)), Var("literal", "%uint_0", 0, Index(-1))>>,
<<Var("local", "%round_robin", "", Index(-1)), Var("literal", "%uint_0", 0, Index(-1))>>,
<<Var("local", "%num_testing_subgroups", "", Index(-1)), Var("literal", "%uint_2", 2, Index(-1))>>,
<<Var("local", "%36", "", Index(-1)), Var("local", "%workgroup_id", "", Index(-1)), Var("local", "%num_testing_subgroups", "", Index(-1))>>,
<<Var("local", "%38", "", Index(-1)), Var("local", "%36", "", Index(-1)), Var("literal", "%uint_0", 0, Index(-1))>>,
<<Var("local", "%40", "", Index(-1)), Var("local", "%subgroup_id", "", Index(-1)), Var("literal", "%uint_0", 0, Index(-1))>>,
<<Var("local", "%41", "", Index(-1)), Var("local", "%38", "", Index(-1)), Var("local", "%40", "", Index(-1))>>,
<<Var("literal", "%43", 86, Index(-1))>>,
<<Var("local", "%41", "", Index(-1)), Var("literal", "%42", 32, Index(-1)), Var("literal", "%43", 86, Index(-1))>>,
<<Var("global", "%42", 32, Index(-1))>>,
<<Var("local", "%terminate", "", Index(-1)), Var("literal", "%int_0", 0, Index(-1))>>,
<<Var("literal", "%48", 35, Index(-1))>>,
<<Var("global", "%48", 35, Index(-1))>>,
<<Var("literal", "%50", 84, Index(-1)), Var("literal", "%51", 82, Index(-1))>>,
<<Var("literal", "%52", 38, Index(-1))>>,
<<Var("global", "%52", 38, Index(-1))>>,
<<Var("literal", "%true", TRUE, Index(-1)), Var("literal", "%49", 40, Index(-1)), Var("literal", "%50", 84, Index(-1))>>,
<<Var("global", "%49", 40, Index(-1))>>,
<<Var("local", "%56", "", Index(-1)), Var("local", "%terminate", "", Index(-1)), Var("literal", "%int_1", 1, Index(-1))>>,
<<Var("local", "%58", "", Index(-1)), Var("literal", "%uint_3", "subgroup", Index(-1)), Var("local", "%56", "", Index(-1))>>,
<<Var("literal", "%60", 47, Index(-1))>>,
<<Var("local", "%58", "", Index(-1)), Var("literal", "%59", 45, Index(-1)), Var("literal", "%60", 47, Index(-1))>>,
<<Var("global", "%59", 45, Index(-1))>>,
<<Var("literal", "%50", 84, Index(-1))>>,
<<Var("global", "%60", 47, Index(-1))>>,
<<Var("local", "%67", "", Index(-1)), Var("local", "%round_robin", "", Index(-1)), Var("local", "%subgroup_size", "", Index(-1))>>,
<<Var("global", "%pickthread", "", Index(-1)), Var("local", "%67", "", Index(-1))>>,
<<Var("local", "%74", "", Index(-1)), Var("global", "%pickthread", "", Index(-1)), Var("local", "%gl_SubgroupInvocationID", "", Index(-1))>>,
<<Var("literal", "%76", 75, Index(-1))>>,
<<Var("local", "%74", "", Index(-1)), Var("literal", "%75", 53, Index(-1)), Var("literal", "%76", 75, Index(-1))>>,
<<Var("global", "%75", 53, Index(-1))>>,
<<Var("literal", "%80", 73, Index(-1))>>,
<<Var("local", "%pc", "", Index(-1)), Var("literal", "%80", 73, Index(-1)), <<Var("literal", "", 0, Index(-1)), Var("literal", "", 1, Index(-1)) >>, <<Var("literal", "%78", 56, Index(-1)), Var("literal", "%79", 70, Index(-1)) >>>>,
<<Var("global", "%78", 56, Index(-1))>>,
<<Var("local", "%86", "", Index(-1)), Var("global", "%out_buf1", "", Index(-1)), Var("literal", "%uint_0", 0, Index(-1))>>,
<<Var("local", "%87", "", Index(-1)), Var("local", "%86", "", Index(-1)), Var("literal", "%uint_0", 0, Index(-1))>>,
<<Var("literal", "%89", 68, Index(-1))>>,
<<Var("local", "%87", "", Index(-1)), Var("literal", "%88", 61, Index(-1)), Var("literal", "%90", 64, Index(-1))>>,
<<Var("global", "%88", 61, Index(-1))>>,
<<Var("local", "%pc", "", Index(-1)), Var("literal", "%uint_0", 0, Index(-1))>>,
<<Var("literal", "%89", 68, Index(-1))>>,
<<Var("global", "%90", 64, Index(-1))>>,
<<Var("local", "%92", "", Index(-1)), Var("local", "%pc", "", Index(-1)), Var("literal", "%uint_1", 1, Index(-1))>>,
<<Var("local", "%pc", "", Index(-1)), Var("local", "%92", "", Index(-1))>>,
<<Var("literal", "%89", 68, Index(-1))>>,
<<Var("global", "%89", 68, Index(-1))>>,
<<Var("literal", "%80", 73, Index(-1))>>,
<<Var("global", "%79", 70, Index(-1))>>,
<<Var("local", "%terminate", "", Index(-1)), Var("literal", "%int_1", 1, Index(-1))>>,
<<Var("literal", "%80", 73, Index(-1))>>,
<<Var("global", "%80", 73, Index(-1))>>,
<<Var("literal", "%76", 75, Index(-1))>>,
<<Var("global", "%76", 75, Index(-1))>>,
<<Var("local", "%97", "", Index(-1)), Var("local", "%round_robin", "", Index(-1)), Var("literal", "%uint_1", 1, Index(-1))>>,
<<Var("local", "%99", "", Index(-1)), Var("local", "%97", "", Index(-1)), Var("local", "%subgroup_size", "", Index(-1))>>,
<<Var("local", "%round_robin", "", Index(-1)), Var("local", "%99", "", Index(-1))>>,
<<Var("local", "%103", "", Index(-1)), Var("literal", "%uint_3", "subgroup", Index(-1)), Var("local", "%pc", "", Index(-1)), Var("global", "%pickthread", "", Index(-1))>>,
<<Var("local", "%pc", "", Index(-1)), Var("local", "%103", "", Index(-1))>>,
<<Var("literal", "%51", 82, Index(-1))>>,
<<Var("global", "%51", 82, Index(-1))>>,
<<Var("literal", "%48", 35, Index(-1))>>,
<<Var("global", "%50", 84, Index(-1))>>,
<<Var("literal", "%43", 86, Index(-1))>>,
<<Var("global", "%43", 86, Index(-1))>>,
<<Var("local", "%106", "", Index(-1)), Var("local", "%workgroup_id", "", Index(-1)), Var("local", "%num_testing_subgroups", "", Index(-1))>>,
<<Var("local", "%107", "", Index(-1)), Var("local", "%106", "", Index(-1)), Var("literal", "%uint_1", 1, Index(-1))>>,
<<Var("local", "%109", "", Index(-1)), Var("local", "%subgroup_id", "", Index(-1)), Var("literal", "%uint_0", 0, Index(-1))>>,
<<Var("local", "%110", "", Index(-1)), Var("local", "%107", "", Index(-1)), Var("local", "%109", "", Index(-1))>>,
<<Var("literal", "%112", 147, Index(-1))>>,
<<Var("local", "%110", "", Index(-1)), Var("literal", "%111", 93, Index(-1)), Var("literal", "%112", 147, Index(-1))>>,
<<Var("global", "%111", 93, Index(-1))>>,
<<Var("local", "%terminate_0", "", Index(-1)), Var("literal", "%int_0", 0, Index(-1))>>,
<<Var("literal", "%114", 96, Index(-1))>>,
<<Var("global", "%114", 96, Index(-1))>>,
<<Var("literal", "%116", 145, Index(-1)), Var("literal", "%117", 143, Index(-1))>>,
<<Var("literal", "%118", 99, Index(-1))>>,
<<Var("global", "%118", 99, Index(-1))>>,
<<Var("literal", "%true", TRUE, Index(-1)), Var("literal", "%115", 101, Index(-1)), Var("literal", "%116", 145, Index(-1))>>,
<<Var("global", "%115", 101, Index(-1))>>,
<<Var("local", "%120", "", Index(-1)), Var("local", "%terminate_0", "", Index(-1)), Var("literal", "%int_1", 1, Index(-1))>>,
<<Var("local", "%121", "", Index(-1)), Var("literal", "%uint_3", "subgroup", Index(-1)), Var("local", "%120", "", Index(-1))>>,
<<Var("literal", "%123", 108, Index(-1))>>,
<<Var("local", "%121", "", Index(-1)), Var("literal", "%122", 106, Index(-1)), Var("literal", "%123", 108, Index(-1))>>,
<<Var("global", "%122", 106, Index(-1))>>,
<<Var("literal", "%116", 145, Index(-1))>>,
<<Var("global", "%123", 108, Index(-1))>>,
<<Var("local", "%127", "", Index(-1)), Var("local", "%round_robin", "", Index(-1)), Var("local", "%subgroup_size", "", Index(-1))>>,
<<Var("global", "%pickthread", "", Index(-1)), Var("local", "%127", "", Index(-1))>>,
<<Var("local", "%132", "", Index(-1)), Var("global", "%pickthread", "", Index(-1)), Var("local", "%gl_SubgroupInvocationID", "", Index(-1))>>,
<<Var("literal", "%134", 136, Index(-1))>>,
<<Var("local", "%132", "", Index(-1)), Var("literal", "%133", 114, Index(-1)), Var("literal", "%134", 136, Index(-1))>>,
<<Var("global", "%133", 114, Index(-1))>>,
<<Var("literal", "%138", 134, Index(-1))>>,
<<Var("local", "%pc", "", Index(-1)), Var("literal", "%138", 134, Index(-1)), <<Var("literal", "", 0, Index(-1)), Var("literal", "", 1, Index(-1)) >>, <<Var("literal", "%136", 117, Index(-1)), Var("literal", "%137", 131, Index(-1)) >>>>,
<<Var("global", "%136", 117, Index(-1))>>,
<<Var("local", "%140", "", Index(-1)), Var("global", "%out_buf1", "", Index(-1)), Var("literal", "%uint_1", 1, Index(-1))>>,
<<Var("local", "%141", "", Index(-1)), Var("local", "%140", "", Index(-1)), Var("literal", "%uint_0", 0, Index(-1))>>,
<<Var("literal", "%143", 129, Index(-1))>>,
<<Var("local", "%141", "", Index(-1)), Var("literal", "%142", 122, Index(-1)), Var("literal", "%144", 125, Index(-1))>>,
<<Var("global", "%142", 122, Index(-1))>>,
<<Var("local", "%pc", "", Index(-1)), Var("literal", "%uint_0", 0, Index(-1))>>,
<<Var("literal", "%143", 129, Index(-1))>>,
<<Var("global", "%144", 125, Index(-1))>>,
<<Var("local", "%146", "", Index(-1)), Var("local", "%pc", "", Index(-1)), Var("literal", "%uint_1", 1, Index(-1))>>,
<<Var("local", "%pc", "", Index(-1)), Var("local", "%146", "", Index(-1))>>,
<<Var("literal", "%143", 129, Index(-1))>>,
<<Var("global", "%143", 129, Index(-1))>>,
<<Var("literal", "%138", 134, Index(-1))>>,
<<Var("global", "%137", 131, Index(-1))>>,
<<Var("local", "%terminate_0", "", Index(-1)), Var("literal", "%int_1", 1, Index(-1))>>,
<<Var("literal", "%138", 134, Index(-1))>>,
<<Var("global", "%138", 134, Index(-1))>>,
<<Var("literal", "%134", 136, Index(-1))>>,
<<Var("global", "%134", 136, Index(-1))>>,
<<Var("local", "%151", "", Index(-1)), Var("local", "%round_robin", "", Index(-1)), Var("literal", "%uint_1", 1, Index(-1))>>,
<<Var("local", "%153", "", Index(-1)), Var("local", "%151", "", Index(-1)), Var("local", "%subgroup_size", "", Index(-1))>>,
<<Var("local", "%round_robin", "", Index(-1)), Var("local", "%153", "", Index(-1))>>,
<<Var("local", "%157", "", Index(-1)), Var("literal", "%uint_3", "subgroup", Index(-1)), Var("local", "%pc", "", Index(-1)), Var("global", "%pickthread", "", Index(-1))>>,
<<Var("local", "%pc", "", Index(-1)), Var("local", "%157", "", Index(-1))>>,
<<Var("literal", "%117", 143, Index(-1))>>,
<<Var("global", "%117", 143, Index(-1))>>,
<<Var("literal", "%114", 96, Index(-1))>>,
<<Var("global", "%116", 145, Index(-1))>>,
<<Var("literal", "%112", 147, Index(-1))>>,
<<Var("global", "%112", 147, Index(-1))>>,
<<Var("literal", "%uint_2", "workgroup", Index(-1))>>,
<<>>>>]



EntryLabel == Min({idx \in 1..Len(ThreadInstructions[1]) : ThreadInstructions[1][idx] = "OpLabel"})
CFGEdges == {
<<47, 75>>, 
<<61, 68>>, 
<<101, 108>>, 
<<117, 122>>, 
<<114, 134>>, 
<<35, 84>>, 
<<117, 125>>, 
<<114, 131>>, 
<<53, 70>>, 
<<73, 75>>, 
<<134, 136>>, 
<<56, 64>>, 
<<86, 147>>, 
<<96, 99>>, 
<<96, 145>>, 
<<70, 73>>, 
<<101, 106>>, 
<<108, 136>>, 
<<53, 73>>, 
<<56, 68>>, 
<<7, 86>>, 
<<45, 84>>, 
<<93, 96>>, 
<<7, 32>>, 
<<99, 101>>, 
<<106, 145>>, 
<<35, 82>>, 
<<114, 117>>, 
<<117, 129>>, 
<<47, 53>>, 
<<53, 56>>, 
<<40, 45>>, 
<<56, 61>>, 
<<145, 147>>, 
<<99, 145>>, 
<<40, 47>>, 
<<38, 84>>, 
<<125, 129>>, 
<<131, 134>>, 
<<84, 86>>, 
<<68, 73>>, 
<<86, 93>>, 
<<143, 96>>, 
<<122, 129>>, 
<<35, 38>>, 
<<129, 134>>, 
<<32, 35>>, 
<<38, 40>>, 
<<108, 114>>, 
<<75, 82>>, 
<<96, 143>>, 
<<136, 143>>, 
<<64, 68>>, 
<<82, 35>>
}
CFGSuccessors == {
<<145, {
147}>>,
<<136, {
143}>>,
<<40, {
45,47}>>,
<<47, {
53,75}>>,
<<56, {
61,64,68}>>,
<<82, {
35}>>,
<<99, {
145,101}>>,
<<7, {
86,32}>>,
<<134, {
136}>>,
<<68, {
73}>>,
<<114, {
117,131,134}>>,
<<131, {
134}>>,
<<101, {
106,108}>>,
<<45, {
84}>>,
<<96, {
143,99,145}>>,
<<106, {
145}>>,
<<93, {
96}>>,
<<125, {
129}>>,
<<38, {
84,40}>>,
<<53, {
56,70,73}>>,
<<61, {
68}>>,
<<84, {
86}>>,
<<35, {
38,84,82}>>,
<<129, {
134}>>,
<<32, {
35}>>,
<<108, {
114,136}>>,
<<73, {
75}>>,
<<86, {
147,93}>>,
<<122, {
129}>>,
<<117, {
125,122,129}>>,
<<64, {
68}>>,
<<70, {
73}>>,
<<143, {
96}>>,
<<75, {
82}>>
}
CFGPredecessors == {
<<40, {
38}>>,
<<68, {
64,56,61}>>,
<<86, {
84,7}>>,
<<45, {
40}>>,
<<99, {
96}>>,
<<38, {
35}>>,
<<35, {
82,32}>>,
<<136, {
108,134}>>,
<<56, {
53}>>,
<<131, {
114}>>,
<<82, {
75,35}>>,
<<134, {
129,114,131}>>,
<<64, {
56}>>,
<<93, {
86}>>,
<<101, {
99}>>,
<<108, {
101}>>,
<<117, {
114}>>,
<<32, {
7}>>,
<<75, {
73,47}>>,
<<106, {
101}>>,
<<114, {
108}>>,
<<147, {
145,86}>>,
<<96, {
143,93}>>,
<<125, {
117}>>,
<<129, {
122,117,125}>>,
<<145, {
106,99,96}>>,
<<53, {
47}>>,
<<73, {
70,68,53}>>,
<<61, {
56}>>,
<<122, {
117}>>,
<<47, {
40}>>,
<<143, {
136,96}>>,
<<84, {
45,35,38}>>,
<<70, {
53}>>
}
Dominated == {
[node |-> 134,
dominated |-> {
134}],
[node |-> 125,
dominated |-> {
125}],
[node |-> 145,
dominated |-> {
145}],
[node |-> 56,
dominated |-> {
61,68,64,56}],
[node |-> 38,
dominated |-> {
73,38,70,68,47,40,64,61,45,56,53,75}],
[node |-> 64,
dominated |-> {
64}],
[node |-> 131,
dominated |-> {
131}],
[node |-> 47,
dominated |-> {
61,73,53,64,68,75,56,47,70}],
[node |-> 96,
dominated |-> {
131,106,143,117,145,101,114,134,96,108,136,125,122,129,99}],
[node |-> 106,
dominated |-> {
106}],
[node |-> 129,
dominated |-> {
129}],
[node |-> 101,
dominated |-> {
129,114,134,106,101,136,131,125,108,117,122}],
[node |-> 108,
dominated |-> {
136,129,114,122,131,108,134,117,125}],
[node |-> 40,
dominated |-> {
75,56,40,70,68,61,45,47,64,53,73}],
[node |-> 53,
dominated |-> {
64,73,61,68,70,56,53}],
[node |-> 68,
dominated |-> {
68}],
[node |-> 70,
dominated |-> {
70}],
[node |-> 75,
dominated |-> {
75}],
[node |-> 7,
dominated |-> {
47,147,64,131,56,117,45,145,129,40,106,75,70,73,61,32,84,35,143,122,114,125,86,99,7,134,38,68,93,101,108,96,136,82,53}],
[node |-> 147,
dominated |-> {
147}],
[node |-> 73,
dominated |-> {
73}],
[node |-> 117,
dominated |-> {
122,117,125,129}],
[node |-> 136,
dominated |-> {
136}],
[node |-> 84,
dominated |-> {
84}],
[node |-> 35,
dominated |-> {
47,45,73,56,68,53,70,82,84,64,61,75,40,35,38}],
[node |-> 122,
dominated |-> {
122}],
[node |-> 32,
dominated |-> {
40,68,75,47,35,82,64,32,45,70,84,56,73,53,38,61}],
[node |-> 93,
dominated |-> {
96,101,93,117,108,114,122,145,99,131,136,134,129,106,125,143}],
[node |-> 82,
dominated |-> {
82}],
[node |-> 99,
dominated |-> {
108,114,136,106,131,134,101,125,122,99,129,117}],
[node |-> 114,
dominated |-> {
122,125,117,114,134,129,131}],
[node |-> 61,
dominated |-> {
61}],
[node |-> 143,
dominated |-> {
143}],
[node |-> 45,
dominated |-> {
45}],
[node |-> 86,
dominated |-> {
129,99,101,114,147,117,108,96,131,122,134,86,93,145,106,125,143,136}]
}
PostDominated == {
[node |-> 75,
postDominated |-> {
53,75,64,68,73,70,61,47,56}],
[node |-> 96,
postDominated |-> {
93,117,143,108,131,114,134,122,96,125,129,136}],
[node |-> 131,
postDominated |-> {
131}],
[node |-> 68,
postDominated |-> {
64,56,68,61}],
[node |-> 147,
postDominated |-> {
61,38,131,40,64,122,68,136,96,32,145,93,56,82,143,117,53,7,75,108,134,47,70,73,129,45,114,35,125,99,86,101,106,147,84}],
[node |-> 145,
postDominated |-> {
145,136,96,134,129,122,93,106,143,117,131,108,99,125,101,114}],
[node |-> 70,
postDominated |-> {
70}],
[node |-> 38,
postDominated |-> {
38}],
[node |-> 40,
postDominated |-> {
40}],
[node |-> 7,
postDominated |-> {
7}],
[node |-> 114,
postDominated |-> {
114}],
[node |-> 129,
postDominated |-> {
125,122,129,117}],
[node |-> 106,
postDominated |-> {
106}],
[node |-> 73,
postDominated |-> {
68,70,56,73,61,64,53}],
[node |-> 64,
postDominated |-> {
64}],
[node |-> 143,
postDominated |-> {
117,108,122,134,143,125,131,129,136,114}],
[node |-> 125,
postDominated |-> {
125}],
[node |-> 93,
postDominated |-> {
93}],
[node |-> 117,
postDominated |-> {
117}],
[node |-> 86,
postDominated |-> {
32,86,64,70,38,53,7,73,61,84,45,56,35,82,68,75,40,47}],
[node |-> 82,
postDominated |-> {
82,73,68,70,53,47,64,61,75,56}],
[node |-> 32,
postDominated |-> {
32}],
[node |-> 53,
postDominated |-> {
53}],
[node |-> 84,
postDominated |-> {
47,68,40,84,70,75,45,73,61,56,82,35,38,32,53,64}],
[node |-> 56,
postDominated |-> {
56}],
[node |-> 45,
postDominated |-> {
45}],
[node |-> 136,
postDominated |-> {
129,131,117,125,134,136,114,108,122}],
[node |-> 47,
postDominated |-> {
47}],
[node |-> 101,
postDominated |-> {
101}],
[node |-> 61,
postDominated |-> {
61}],
[node |-> 108,
postDominated |-> {
108}],
[node |-> 99,
postDominated |-> {
99}],
[node |-> 134,
postDominated |-> {
131,134,125,114,122,117,129}],
[node |-> 122,
postDominated |-> {
122}],
[node |-> 35,
postDominated |-> {
56,47,73,82,32,35,70,53,64,61,75,68}]
}
ControlFlowConstructs == {
[
constructType |-> "Selection",
headerBlock |-> 7,
mergeBlock |-> 86,
continueTarget |-> -1,
blocks |-> {
82,
47,
45,
70,
32,
56,
73,
7,
35,
84,
40,
64,
68,
61,
38,
75,
53
}
]
,
[
constructType |-> "Loop",
headerBlock |-> 35,
mergeBlock |-> 84,
continueTarget |-> 82,
blocks |-> {
64,
75,
47,
73,
35,
68,
70,
45,
56,
40,
53,
38,
61
}
]
,
[
constructType |-> "Continue",
headerBlock |-> 82,
mergeBlock |-> -1,
continueTarget |-> 82,
blocks |-> {
82
}
]
,
[
constructType |-> "Selection",
headerBlock |-> 40,
mergeBlock |-> 47,
continueTarget |-> -1,
blocks |-> {
40,
45
}
]
,
[
constructType |-> "Selection",
headerBlock |-> 47,
mergeBlock |-> 75,
continueTarget |-> -1,
blocks |-> {
64,
70,
53,
61,
73,
68,
56,
47
}
]
,
[
constructType |-> "Switch",
headerBlock |-> 53,
mergeBlock |-> 73,
continueTarget |-> -1,
blocks |-> {
61,
68,
64,
53,
70,
56
}
]
,
[
constructType |-> "Case",
headerBlock |-> 70,
mergeBlock |-> 73,
continueTarget |-> -1,
blocks |-> {
70
}
]
,
[
constructType |-> "Case",
headerBlock |-> 56,
mergeBlock |-> 73,
continueTarget |-> -1,
blocks |-> {
68,
64,
56,
61
}
]
,
[
constructType |-> "Case",
headerBlock |-> 73,
mergeBlock |-> 73,
continueTarget |-> -1,
blocks |-> {
}
]
,
[
constructType |-> "Selection",
headerBlock |-> 56,
mergeBlock |-> 68,
continueTarget |-> -1,
blocks |-> {
56,
64,
61
}
]
,
[
constructType |-> "Selection",
headerBlock |-> 86,
mergeBlock |-> 147,
continueTarget |-> -1,
blocks |-> {
129,
93,
145,
143,
99,
122,
96,
101,
125,
131,
106,
108,
136,
134,
114,
117,
86
}
]
,
[
constructType |-> "Loop",
headerBlock |-> 96,
mergeBlock |-> 145,
continueTarget |-> 143,
blocks |-> {
134,
101,
114,
125,
106,
96,
117,
122,
129,
99,
136,
131,
108
}
]
,
[
constructType |-> "Continue",
headerBlock |-> 143,
mergeBlock |-> -1,
continueTarget |-> 143,
blocks |-> {
143
}
]
,
[
constructType |-> "Selection",
headerBlock |-> 101,
mergeBlock |-> 108,
continueTarget |-> -1,
blocks |-> {
106,
101
}
]
,
[
constructType |-> "Selection",
headerBlock |-> 108,
mergeBlock |-> 136,
continueTarget |-> -1,
blocks |-> {
131,
122,
108,
129,
125,
114,
134,
117
}
]
,
[
constructType |-> "Switch",
headerBlock |-> 114,
mergeBlock |-> 134,
continueTarget |-> -1,
blocks |-> {
125,
129,
122,
131,
117,
114
}
]
,
[
constructType |-> "Case",
headerBlock |-> 131,
mergeBlock |-> 134,
continueTarget |-> -1,
blocks |-> {
131
}
]
,
[
constructType |-> "Case",
headerBlock |-> 117,
mergeBlock |-> 134,
continueTarget |-> -1,
blocks |-> {
122,
117,
129,
125
}
]
,
[
constructType |-> "Case",
headerBlock |-> 134,
mergeBlock |-> 134,
continueTarget |-> -1,
blocks |-> {
}
]
,
[
constructType |-> "Selection",
headerBlock |-> 117,
mergeBlock |-> 129,
continueTarget |-> -1,
blocks |-> {
117,
125,
122
}
]

}
Blocks == <<
[
opLabelIdx |-> 7,
terminatedInstrIdx |-> 31,
tangle |-> <<
{1},
{2}
>>,
merge |-> FALSE,
initialized |-> <<
TRUE,
TRUE
>>,
constructType |-> "Selection",
mergeBlock |-> 86,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 32,
terminatedInstrIdx |-> 34,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "None",
mergeBlock |-> -1,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 35,
terminatedInstrIdx |-> 37,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "Loop",
mergeBlock |-> 84,
continueBlock |-> 82,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 38,
terminatedInstrIdx |-> 39,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "None",
mergeBlock |-> -1,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 40,
terminatedInstrIdx |-> 44,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "Selection",
mergeBlock |-> 47,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 45,
terminatedInstrIdx |-> 46,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "None",
mergeBlock |-> -1,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 47,
terminatedInstrIdx |-> 52,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "Selection",
mergeBlock |-> 75,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 53,
terminatedInstrIdx |-> 55,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "Switch",
mergeBlock |-> 73,
continueBlock |-> -1,
defaultBlock |-> 73,
caseBlocks |-> <<
70,
56
>>
]
,
[
opLabelIdx |-> 56,
terminatedInstrIdx |-> 60,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "Selection",
mergeBlock |-> 68,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 61,
terminatedInstrIdx |-> 63,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "None",
mergeBlock |-> -1,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 64,
terminatedInstrIdx |-> 67,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "None",
mergeBlock |-> -1,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 68,
terminatedInstrIdx |-> 69,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "None",
mergeBlock |-> -1,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 70,
terminatedInstrIdx |-> 72,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "None",
mergeBlock |-> -1,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 73,
terminatedInstrIdx |-> 74,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "None",
mergeBlock |-> -1,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 75,
terminatedInstrIdx |-> 81,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "None",
mergeBlock |-> -1,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 82,
terminatedInstrIdx |-> 83,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "None",
mergeBlock |-> -1,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 84,
terminatedInstrIdx |-> 85,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "None",
mergeBlock |-> -1,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 86,
terminatedInstrIdx |-> 92,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "Selection",
mergeBlock |-> 147,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 93,
terminatedInstrIdx |-> 95,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "None",
mergeBlock |-> -1,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 96,
terminatedInstrIdx |-> 98,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "Loop",
mergeBlock |-> 145,
continueBlock |-> 143,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 99,
terminatedInstrIdx |-> 100,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "None",
mergeBlock |-> -1,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 101,
terminatedInstrIdx |-> 105,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "Selection",
mergeBlock |-> 108,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 106,
terminatedInstrIdx |-> 107,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "None",
mergeBlock |-> -1,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 108,
terminatedInstrIdx |-> 113,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "Selection",
mergeBlock |-> 136,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 114,
terminatedInstrIdx |-> 116,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "Switch",
mergeBlock |-> 134,
continueBlock |-> -1,
defaultBlock |-> 134,
caseBlocks |-> <<
131,
117
>>
]
,
[
opLabelIdx |-> 117,
terminatedInstrIdx |-> 121,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "Selection",
mergeBlock |-> 129,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 122,
terminatedInstrIdx |-> 124,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "None",
mergeBlock |-> -1,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 125,
terminatedInstrIdx |-> 128,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "None",
mergeBlock |-> -1,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 129,
terminatedInstrIdx |-> 130,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "None",
mergeBlock |-> -1,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 131,
terminatedInstrIdx |-> 133,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "None",
mergeBlock |-> -1,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 134,
terminatedInstrIdx |-> 135,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "None",
mergeBlock |-> -1,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 136,
terminatedInstrIdx |-> 142,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "None",
mergeBlock |-> -1,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 143,
terminatedInstrIdx |-> 144,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "None",
mergeBlock |-> -1,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 145,
terminatedInstrIdx |-> 146,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "None",
mergeBlock |-> -1,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]
,
[
opLabelIdx |-> 147,
terminatedInstrIdx |-> 149,
tangle |-> <<
{},
{}
>>,
merge |-> FALSE,
initialized |-> <<
FALSE,
FALSE
>>,
constructType |-> "None",
mergeBlock |-> -1,
continueBlock |-> -1,
defaultBlock |-> -1,
caseBlocks |-> <<
>>
]

>>
MergeBlocks == {
}

InitDB == DynamicNodeSet = {
DynamicNode(<<{1}, {2}>>, <<{1}, {2}>>, <<{}, {}>>, <<{}, {}>>, 7, 0, <<>>, {})
}


Synchronization == "None"
INSTANCE ProgramConf

(* Inovactions within a tangle are required to execute tangled instruction concurrently, examples or opGroup operations and opControlBarrier  *)
TangledInstructionSet == {"OpControlBarrier, OpGroupAll", "OpGroupAny", "OpGroupNonUniformAll", "OpGroupNonUniformAllEqual", "OpGroupNonUniformAny", "OpGroupNonUniformBroadcast"}
MergedInstructionSet == {"OpLoopMerge", "OpSelectionMerge"}
BlockTerminationInstructionSet == {"OpBranch", "OpBranchConditional", "OpSwitch", "Terminate"}
BranchInstructionSet == {"OpBranch", "OpBranchConditional", "OpSwitch"}
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
    \* LET iterSet ==
    \*     {iter \in DOMAIN iterationsVec : iterationsVec[iter].blockIdx = blockIdx}
    \* IN
    \*     IF iterSet # {} 
    \*     THEN
    \*         LET idx == CHOOSE iter \in iterSet : TRUE
    \*             IN
    \*                 iterationsVec[idx]
    \*     ELSE
    \*         Iteration(blockIdx, 0)
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
    \* /\ Len(left) = Len(right)
    \* /\ \A idx \in 1..Len(left):
    \*     /\ left[idx].blockIdx = right[idx].blockIdx
    \*     /\ left[idx].counter = right[idx].counter

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

\* 1. Push the merge block to the merge stack of current DB.
\* 2. Update the iteration vector of current DB for current thread.
\* LoopMergeUpdate(wgid, t, currentLabelIdx, mergeBlock) ==
\*     LET

\*         currentDB == CurrentDynamicNode(wgid, t)
\*         \* updatedThreadMergeStack == Push(currentDB.mergeStack[t], mergeBlock)
\*         currentIteration == FindIteration(currentLabelIdx, currentDB.children[t], t)
\*         \* if new iteration is created, we need to add it to the iteration vector
\*         \* otherwise we just need to increment the iteration number of top element of the iteration vector
\*         updatedThreadIterationVec == IF currentIteration.iter = 0
\*         THEN 
\*             Push(currentDB.children[t], Iteration(currentLabelIdx, 1))
\*         ELSE 
\*             [currentDB.children[t] EXCEPT ![Len(currentDB.children[t])] = Iteration(currentIteration.blockIdx, currentIteration.iter + 1)]
\*         hasExistingBlock == \E DB \in DynamicNodeSet : DB.labelIdx = currentLabelIdx /\ CanMergeSameIterationVector(updatedThreadIterationVec, DB.children)
\*         filterDynamicNode == {DB \in DynamicNodeSet : t \notin DB.currentThreadSet[wgid]}
\*     IN
\*         \* if we has existing block with the same iteration vector, we need to merge the current block with the existing block
\*         IF hasExistingBlock THEN
\*             {
\*                 IF DB.labelIdx = currentLabelIdx /\ CanMergeSameIterationVector(updatedThreadIterationVec, DB.children)
\*                 THEN
\*                     DynamicNode([DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \union {t}],
\*                     [DB.executeSet EXCEPT ![wgid] = DB.executeSet[wgid] \union {t}],
\*                     [DB.notExecuteSet EXCEPT ![wgid] = DB.notExecuteSet[wgid] \ {t}],
\*                     [DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ {t}],
\*                     DB.labelIdx,
\*                     \* [DB.mergeStack EXCEPT ![t] = updatedThreadMergeStack],
\*                     [DB.children EXCEPT ![t] = updatedThreadIterationVec])
\*                 ELSE 
\*                     DB
\*                 : DB \in filterDynamicNode
\*                 }
\*         ELSE
\*         filterDynamicNode
\*         \union 
\*         (
\*              { DynamicNode(currentDB.currentThreadSet,
\*                         currentDB.executeSet,
\*                         currentDB.notExecuteSet,
\*                         currentDB.unknownSet,
\*                         currentLabelIdx,
\*                         \* currentDB.mergeStack,
\*                         [currentDB.children EXCEPT ![t] = updatedThreadIterationVec])
\*             }
\*         )
        \* {
        \*     IF t \in DB.currentThreadSet[wgid] THEN
        \*       DynamicNode(currentDB.currentThreadSet,
        \*                 currentDB.executeSet,
        \*                 currentDB.notExecuteSet,
        \*                 currentDB.unknownSet,
        \*                 currentLabelIdx,
        \*                 \* currentDB.mergeStack,
        \*                 [currentDB.children EXCEPT ![t] = updatedThreadIterationVec])
            
        \*     ELSE 
        \*         DB
        \*     : DB \in DynamicNodeSet
        \* }


\* opLabelIdxSet is used to update the children of the current DB
\* f
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
        \* currentIteration == FindIteration(currentDB.labelIdx, currentDB.children, t)
        \* if new iteration is created, we need to add it to the iteration vector
        \* otherwise we just need to increment the iteration number of top element of the iteration vector
        \* updatedThreadIterationVec == IF currentIteration.iter = 0
        \* THEN 
        \*     Push(currentDB.children, Iteration(currentDB.labelIdx, 1))
        \* ELSE 
        \*     [currentDB.children EXCEPT ![Len(currentDB.children)] = Iteration(currentIteration.blockIdx, currentIteration.iter + 1)]
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
        \* We only update the merge stack if the current block is a header block and if firstly reach the divergence
        \* globalCounter is only updated when we firstly reach the divergence
        updatedCounter == currentCounter + Cardinality(updatedChildren) - Cardinality(currentChildren) + Len(updatedMergeStack) - Len(currentMergeStack)
        \* isLoopHeader == IsLoopHeaderBlock(currentBlock)
        \* loopBranchIdx == IF isLoopHeader THEN
        \*     ThreadArguments[t][pc][1].value
        \* ELSE
        \*     -1
        
        mergeBlock == currentBlock.mergeBlock
        \* exsiting dynamic blocks for false labels
        \* zheyuan: update this
        existingFalseLabelIdxSet == {
            falselabelIdx \in falseLabelIdxSet: 
                \E DB \in DynamicNodeSet: DB.labelIdx = falselabelIdx /\ \E child \in updatedChildren: child.blockIdx = DB.labelIdx /\ child.counter = DB.id
                
        }
        \* we want to update the blocks in loop construct as well as the continue target
        \* loopConstructUpdate == 
        \*     IF IsMergeBlockOfLoop(chosenBranchIdx) THEN
        \*         LET loopConstruct == BlocksInSameLoopConstruct(currentDB.mergeStack[Len(currentDB.mergeStack)].blockIdx, chosenBranchIdx)
        \*         IN
        \*             loopConstruct.blocks \union {loopConstruct.continueTarget}
        \*     ELSE
        \*         {}
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
                DynamicNode([DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \ {t}],
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
                DynamicNode([DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \ {t}],
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
                    \* /\ ((IsMergeBlock(chosenBranchIdx) /\ updatedMergeStack[Len(updatedMergeStack)].blockIdx = DB.labelIdx /\ updatedMergeStack[Len(updatedMergeStack)].counter = DB.id) 
                    /\ \E child \in updatedChildren: child.blockIdx = DB.labelIdx /\ child.counter = DB.id
            THEN
                DynamicNode([DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \union {t}],
                    [DB.executeSet EXCEPT ![wgid] = DB.executeSet[wgid] \union {t}],
                    DB.notExecuteSet,
                    [DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ {t}],
                    DB.labelIdx,
                    DB.id,
                    DB.mergeStack,
                    DB.children)
                \* IF  IsMergeBlock(chosenBranchIdx) /\ SameMergeStack(DB.mergeStack, Pop(updatedMergeStack)) THEN 
                \*     DynamicNode([DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \union {t}],
                \*         [DB.executeSet EXCEPT ![wgid] = DB.executeSet[wgid] \union {t}],
                \*         DB.notExecuteSet,
                \*         [DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ {t}],
                \*         DB.labelIdx,
                \*         DB.id,
                \*         DB.mergeStack,
                \*         DB.children)
                \* \* if the choosen branch index is the header of a construct
                \* \* zheyuan: has problem here
                \* ELSE IF IsConstructHeaderBlock(DB.labelIdx) /\ SameMergeStack(DB.mergeStack, updatedMergeStack) THEN
                \*     DynamicNode([DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \union {t}],
                \*         [DB.executeSet EXCEPT ![wgid] = DB.executeSet[wgid] \union {t}],
                \*         DB.notExecuteSet,
                \*         [DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ {t}],
                \*         DB.labelIdx,
                \*         DB.id,
                \*         DB.mergeStack,
                \*         DB.children)
                \* ELSE IF IsMergeBlock(DB.labelIdx) = FALSE /\ SameMergeStack(DB.mergeStack, updatedMergeStack) THEN 
                \*     DynamicNode([DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \union {t}],
                \*         [DB.executeSet EXCEPT ![wgid] = DB.executeSet[wgid] \union {t}],
                \*         DB.notExecuteSet,
                \*         [DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ {t}],
                \*         DB.labelIdx,
                \*         DB.id,
                \*         DB.mergeStack,
                \*         DB.children)
                \* ELSE
                \*     DB
            \* Encounter the block that is not choosen by the branch instruction
            \* we don't update the existing set for merge block as threads will eventually reach there unless they terminate early
            ELSE IF DB.labelIdx \in falseLabelIdxSet
                /\ IsMergeBlock(DB.labelIdx) = FALSE
                /\ \E child \in updatedChildren: child.blockIdx = DB.labelIdx /\ child.counter = DB.id
                \* /\ (\/ (SameMergeStack(DB.mergeStack, currentDB.mergeStack))
                \*     \/  ( SameMergeStack(DB.mergeStack, updatedMergeStack)))
            
            THEN
                DynamicNode(DB.currentThreadSet,
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
                \* zheyuan: is this even possible to happen? constructUpdate is non-empty only if we choose to exit the construct, try to test it
                IF chosenBranchIdx \in constructUpdate THEN
                    {DynamicNode([wg \in 1..NumWorkGroups |-> {}],
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
                        DynamicNode([wg \in 1..NumWorkGroups |-> IF wg = wgid THEN {t} ELSE {}],
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
                \* if the chosen block is a new block for loop body, we need to update the iteration vector. 
                \* we can only go to the loop branch at loop header block, hence if a thread is not executing the loop header block, it will also not be executing the loop body
                \* ELSE IF chosenBranchIdx = loopBranchIdx THEN
                \*     {
                \*         DynamicNode([wg \in 1..NumWorkGroups |-> IF wg = wgid THEN {t} ELSE {}],
                \*                     [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN {t} ELSE {}],
                \*                     \* zheyuan: do we need to update the notExecuteSet here? or just leave it blank
                \*                     [currentDB.notExecuteSet EXCEPT ![wgid] = currentDB.notExecuteSet[wgid] \ {t}],
                \*                     \* [currentDB.unknownSet EXCEPT ![wgid] = currentDB.unknownSet[wgid] \ {t}],
                \*                     [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN unionSet[wgid] \ {t}  ELSE unionSet[wg]],
                \*                     chosenBranchIdx,
                \*                     LET child == CHOOSE child \in updatedChildren: child.blockIdx = chosenBranchIdx
                \*                     IN
                \*                         child.counter,
                \*                     updatedMergeStack,
                \*                     {})
                \*     }
                ELSE
                    {
                        DynamicNode([wg \in 1..NumWorkGroups |-> IF wg = wgid THEN {t} ELSE {}],
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
                DynamicNode([wg \in 1..NumWorkGroups |-> {}],
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
                DynamicNode([wg \in 1..NumWorkGroups |-> {}], \* currently no thread is executing the false block
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
            \* ELSE IF IsMergeBlock(falselabelIdx) = TRUE THEN 
            \*     DynamicNode([wg \in 1..NumWorkGroups |-> {}], \* currently no thread is executing the false block
            \*                 [wg \in 1..NumWorkGroups |-> {}], \* currently no thread has executed the false block
            \*                 \* current thread is not executed in the false block, but we don't know if the threads executed in precedessor DB will execute the block or not
            \*                 [wg \in 1..NumWorkGroups |-> {}],
            \*                 \* we don't know if the threads executed in precedessor DB will execute the block or not
            \*                 \* [wg \in 1..NumWorkGroups |-> ThreadsWithinWorkGroupNonTerminated(wg-1)],
            \*                 [wg \in 1..NumWorkGroups |-> unionSet[wg]],
            \*                 falselabelIdx,
            \*                 currentDB.children)
            \* if the unchosen chosen block is a new block for loop body, we need to update the iteration vector. 
            \* we can only go to the loop branch at loop header block, hence if a thread is not executing the loop header block, it will also not be executing the loop body
            \* ELSE IF falselabelIdx = loopBranchIdx THEN
            \*     DynamicNode([wg \in 1..NumWorkGroups |-> {}], \* currently no thread is executing the false block
            \*                 [wg \in 1..NumWorkGroups |-> {}], \* currently no thread has executed the false block
            \*                 \* current thread is not executed in the false block, but we don't know if the threads executed in precedessor DB will execute the block or not
            \*                 [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN {t} ELSE {}],
            \*                 \* we don't know if the threads executed in precedessor DB will execute the block or not
            \*                 \* [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN ThreadsWithinWorkGroupNonTerminated(wgid-1) \ {t}  ELSE ThreadsWithinWorkGroupNonTerminated(wg-1)],
            \*                 [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN unionSet[wgid] \ {t}  ELSE unionSet[wg]],
            \*                 falselabelIdx,
            \*                 updatedThreadIterationVec)
            ELSE 
                DynamicNode([wg \in 1..NumWorkGroups |-> {}], \* currently no thread is executing the false block
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

TerminateUpdate(wgid, t) ==
    {
        DynamicNode([DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \ {t}],
            DB.executeSet,
            DB.notExecuteSet,
            [DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ {t}],
            DB.labelIdx,
            DB.id,
            DB.mergeStack,
            DB.children)
        : DB \in DynamicNodeSet
    }

InitGPU == 
	globalVars = {
		Var("global", "%test", 0, Index(-1)),
		Var("global", "%out_buf1", 0, Index(-1)),
		Var("global", "%pickthread", 0, Index(-1)),
		Var("global", "%out_buf2", 0, Index(-1))
	}


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


