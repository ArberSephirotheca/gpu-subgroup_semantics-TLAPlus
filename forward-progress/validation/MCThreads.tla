---- MODULE MCThreads ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE TLC
VARIABLES pc, state, threadLocals, globalVars, DynamicNodeSet, globalCounter, snapShotMap

(* Thread Configuration *)
INSTANCE  MCProgram

ThreadState == {"ready", "workgroup", "subgroup", "terminated"}
threadVars == <<pc, state>>

InitThreadVars ==
    /\  pc = [t \in Threads |-> 1]
    /\  state = [t \in Threads |-> "ready"]
    /\  threadLocals = [t \in Threads |-> {}]
    
InitThreads == 
    /\  InitThreadVars

newSnapShot(localPc, localState, localThreadLocals, localGlobalVars, dynamicNodeSet, localCounter) ==
    [
        pc |-> localPc,
        state |-> localState,
        threadLocals |-> localThreadLocals,
        globalVars |-> localGlobalVars,
        \*dynamicNode |-> dynamicNode,
        dynamicNodeSet |-> dynamicNodeSet,
        globalCounter |-> localCounter
    ]

RemoveId(dynamicNode) == [dynamicNode EXCEPT !.id = 0, !.mergeStack = <<>>, !.children = {}, !.sis = EmptySIS]



InitSnapShotMap ==
    LET newDBIds == {db.labelIdx : db \in DynamicNodeSet} IN
         snapShotMap = { newSnapShot(<<>>, <<>>, <<>>, {}, DynamicNodeSet, 1) : db \in DynamicNodeSet}


LowestPcWithinSubgroup(sid, wgid) == Min({pc[tid]: tid \in ThreadsWithinSubgroup(sid, wgid)})

MinThreadWithinWorkGroup(workGroupId) ==
    Min(ThreadsWithinWorkGroup(workGroupId))

cleanIntermediateVar(t) == 
    /\  LET workGroupId == WorkGroupId(t)+1
            currthreadLocals == threadLocals[WorkGroupId(t)+1]
        IN
            LET eliminatedVars == {currVar \in currthreadLocals : currVar.scope = "intermediate"}
            IN
                /\  threadLocals' =  [threadLocals EXCEPT ![workGroupId] = threadLocals[workGroupId] \ eliminatedVars]


 UpdateState(tid, State) ==
     /\  state' = [state EXCEPT ![tid] = State]
    
StateUpdate(wgid, t, newDBSet) ==
    [thread \in Threads |-> 
        IF \E DB \in newDBSet :
            /\ state[thread] # "terminated"
            /\ state[thread] # "ready"
            /\ thread \in DB.currentThreadSet[wgid]
            /\ \A tid \in DB.currentThreadSet[wgid] : pc[tid] = pc[thread] (* /\ ThreadInstructions[1][pc[tid]] \in TangledInstructionSet *) /\ state[tid] = state[thread]
            /\ DB.unknownSet[wgid] = {}
        THEN 
            "ready"
        ELSE
            state[thread]
    ]


Basic(s) ==
  [ pc           |-> s.pc,
    state        |-> s.state,
    threadLocals |-> s.threadLocals,
    globalVars   |-> s.globalVars,
    dynamicNode  |-> s.dynamicNode]

InsertMultipleSnapShots(map, snapshots) ==
    map \cup snapshots

SnapShotUpdate(newDBSet, newState, t, localPc, newCounter) ==
        LET newDBs == newDBSet \ DynamicNodeSet
            newDBIds == {db.labelIdx : db \in newDBs}
            snapShots == {newSnapShot(localPc, newState, threadLocals, globalVars, newDBSet, newCounter)}
        IN
            InsertMultipleSnapShots(snapShotMap, snapShots)

StateUpdateSubgroup(wgid, active_subgroup_threads, newDBSet) ==
    [thread \in Threads |->
        IF thread \in active_subgroup_threads THEN
            "ready"
        ELSE
            state[thread]
    ]

SnapShotUpdateSubgroup(newDBSet, newState, active_subgroup_threads, localPc, newCounter) ==
        LET newDBs == newDBSet \ DynamicNodeSet
            newDBIds == {db.labelIdx : db \in newDBs}
            snapShots == {newSnapShot(localPc, newState, threadLocals, globalVars, newDBSet, newCounter)}
        IN
            InsertMultipleSnapShots(snapShotMap, snapShots)

MeaningfulUpdate(localPc, newState, oldSnapShotMap, newDBSet) ==
    LET newDBs == newDBSet \ DynamicNodeSet
    IN
        { snapshot \in oldSnapShotMap :
                /\ snapshot["pc"] = localPc
                /\ snapshot["state"] = newState
                /\ snapshot["threadLocals"] = threadLocals
                /\ snapshot["globalVars"] = globalVars
        }

GetBackState(localPc, newState, oldSnapShotMap, newDBSet) ==
    CHOOSE snapshot \in oldSnapShotMap:
        /\ snapshot["pc"] = localPc
        /\ snapshot["state"] = newState
        /\ snapshot["threadLocals"] = threadLocals
        /\ snapshot["globalVars"] = globalVars
        /\ snapshot["dynamicNode"] = RemoveId(CHOOSE db \in (newDBSet \ DynamicNodeSet): TRUE)

    

\* https://en.wikipedia.org/wiki/Bitwise_operation#Mathematical_equivalents
RECURSIVE And(_,_,_,_)
LOCAL And(x,y,n,m) == 
        LET exp == 2^n
        IN IF m = 0 
           THEN 0
           ELSE exp * ((x \div exp) % 2) * ((y \div exp) % 2) 
                    + And(x,y,n+1,m \div 2)

x & y == 
    (***************************************************************************)
    (* Bitwise AND of (non-negative) x and y (defined for Nat \cup {0}).       *)
    (***************************************************************************)
    IF x >= y THEN And(x, y, 0, x) ELSE And(y, x, 0, y) \* Infix variant of And(x,y)

-------------------------------------------------------------------------------

RECURSIVE Or(_,_,_,_)
LOCAL Or(x,y,n,m) == 
        LET exp == 2^n
            xdm == (x \div exp) % 2
            ydm == (y \div exp) % 2
        IN IF m = 0 
           THEN 0
           ELSE exp * (((xdm + ydm) + (xdm * ydm)) % 2)
                        + Or(x,y,n+1,m \div 2)

x | y == 
    (***************************************************************************)
    (* Bitwise OR of (non-negative) x and y (defined for Nat \cup {0}).        *)
    (***************************************************************************)
    IF x >= y THEN Or(x, y, 0, x) ELSE Or(y, x, 0, y) \* Infix variant of Or(x,y)

-------------------------------------------------------------------------------

RECURSIVE Xor(_,_,_,_)
LOCAL Xor(x,y,n,m) == 
        LET exp == 2^n
        IN IF m = 0 
           THEN 0
           ELSE exp * (((x \div exp) + (y \div exp)) % 2) 
                    + Xor(x,y,n+1,m \div 2)

x ^^ y ==   \* single "^" already taken by Naturals.tla
    (***************************************************************************)
    (* Bitwise XOR of (non-negative) x and y (defined for Nat \cup {0}).       *)
    (***************************************************************************)
    IF x >= y THEN Xor(x, y, 0, x) ELSE Xor(y, x, 0, y) \* Infix variant of Xor(x,y)

-------------------------------------------------------------------------------

RECURSIVE NotR(_,_,_)
LOCAL NotR(x,n,m) == 
    LET exp == 2^n
        xdm == (x \div exp) % 2
    IN IF m = 0 
        THEN 0
        ELSE exp * ((xdm + 1) % 2)
                    + NotR(x,n+1,m \div 2)

-------------------------------------------------------------------------------

RECURSIVE shiftR(_,_)
shiftR(n,pos) == 
    (***************************************************************************)
    (* Logical bit-shifting the (non-negative) n by pos positions to the right *)
    (* shifting zeros in from the left/MSB (defined for Nat \cup {0}).         *)
    (***************************************************************************)
    IF pos = 0 
    THEN n
    ELSE LET odd(z) == z % 2 = 1
             m == IF odd(n) THEN (n-1) \div 2 ELSE n \div 2
         IN shiftR(m, pos - 1)

RECURSIVE shiftL(_,_)
shiftL(n, pos) ==
    (***************************************************************************)
    (* Logical bit-shifting the (non-negative) n by pos positions to the left   *)
    (* shifting zeros in from the right/LSB.                                  *)
    (***************************************************************************)
    IF pos = 0 
    THEN n
    ELSE shiftL(2 * n, pos - 1)

Assignment(t, vars) == 
    /\  LET workGroupId == WorkGroupId(t)+1
            AssGlobalVars == {var \in vars : var.scope = "global"} 
            AssthreadLocals == {var \in vars : var.scope # "global"}
            currthreadLocals == threadLocals[WorkGroupId(t)+1]
        IN
            \* try to eliminated var with old value and intermediate var
            LET eliminatedthreadLocals == {currVar \in currthreadLocals : \E var \in vars: (currVar.name = var.name /\ currVar.scope = var.scope)}
                eliminatedGlobalVars == {currVar \in globalVars : \E var \in vars: (currVar.name = var.name /\ currVar.scope = var.scope)}
            IN
                /\  threadLocals' =  [threadLocals EXCEPT ![workGroupId] = (threadLocals[workGroupId] \ eliminatedthreadLocals) \union AssthreadLocals]
                /\  globalVars' = (globalVars \ eliminatedGlobalVars) \union AssGlobalVars
                \* /\  Print(AssthreadLocals, TRUE)

\* This is the inner helper function to return the array with updated element. It does not change the next state of the variable
ChangeElementAt(var, index, value) ==
        Var(var.scope, var.name, [currentIndex \in DOMAIN var.value |-> IF currentIndex = index THEN value ELSE var.value[currentIndex] ], var.index)


OpLogicalOr(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                /\  IF operand1Val = TRUE \/ operand2Val = TRUE THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars, DynamicNodeSet, globalCounter, snapShotMap>>

OpLogicalAnd(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                /\  IF operand1Val = TRUE /\ operand2Val = TRUE THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>

OpLogicalEqual(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                /\  IF operand1Val = operand2Val THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>

OpLogicalNotEqual(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                /\  IF operand1Val # operand2Val THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
OpLogicalNot(t, var, operand) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand == Mangle(t, operand)
    IN
        /\  LET operandVal == GetVal(workGroupId, mangledOperand)
            IN
                /\  IF operandVal = FALSE THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>

OpAtomicOr(t, var, pointer, value) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledPointer == Mangle(t, pointer)
        mangledValue == Mangle(t, value)

    IN
        /\  LET pointerVal == GetVal(workGroupId, mangledPointer)
                valueVal == GetVal(workGroupId, mangledValue)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, pointerVal, Index(-1)), Var(mangledPointer.scope, mangledPointer.name, pointerVal | valueVal, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, DynamicNodeSet, globalCounter, snapShotMap>>

OpAtomicOrSync(t, var, pointer, value) ==
    LET mangledVar == Mangle(t, var)
        mangledPointer == Mangle(t, pointer)
        mangledValue == Mangle(t, value)
        workGroupId == WorkGroupId(t) + 1
        sgIdx == SubgroupIndex(t)
        currentPc == pc[t]
        sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
        currentDB == CurrentDynamicNode(workGroupId, t)
        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
        aligned == unknown_subgroup_threads = {} /\ \A sthread \in active_subgroup_threads: pc[sthread] = currentPc
        pointerVal == GetVal(workGroupId, mangledPointer)
        valueVal == GetVal(workGroupId, mangledValue)
        assignmentSet == {Var(mangledVar.scope, mangledVar.name, pointerVal, Index(-1)),
                          Var(mangledPointer.scope, mangledPointer.name, pointerVal | valueVal, Index(-1))}
        remaining == {sthread \in active_subgroup_threads : sthread # t /\ pc[sthread] = currentPc}
    IN
        /\ (IsVariable(mangledVar) \/ IsIntermediate(mangledVar))
        /\ IsVariable(mangledPointer)
        /\ VarExists(workGroupId, mangledPointer)
        /\ IF currentDB.sis[workGroupId][sgIdx][currentPc] = FALSE THEN
                IF ~aligned THEN
                    /\ state' = [state EXCEPT ![t] = "subgroup"]
                    /\ UNCHANGED <<pc, threadLocals, globalVars, DynamicNodeSet, globalCounter, snapShotMap>>
                ELSE
                    LET newDBSet == SetSISInDB(DynamicNodeSet, currentDB, workGroupId, sgIdx, currentPc, TRUE)
                    IN
                        /\ DynamicNodeSet' = newDBSet
                        /\ state' = StateUpdateSubgroup(workGroupId, active_subgroup_threads, newDBSet)
                        /\ UNCHANGED <<pc, threadLocals, globalVars, globalCounter, snapShotMap>>
           ELSE
                LET newDBSet == IF remaining = {}
                                 THEN SetSISInDB(DynamicNodeSet, currentDB, workGroupId, sgIdx, currentPc, FALSE)
                                 ELSE DynamicNodeSet
                IN
                    /\ Assignment(t, assignmentSet)
                    /\ pc' = [pc EXCEPT ![t] = pc[t] + 1]
                    /\ DynamicNodeSet' = newDBSet
                    /\ state' = [state EXCEPT ![t] = "ready"]
                    /\ UNCHANGED <<globalCounter, snapShotMap>>


OpAtomicAnd(t, var, pointer, value) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledPointer == Mangle(t, pointer)
        mangledValue == Mangle(t, value)

    IN
        /\  LET pointerVal == GetVal(workGroupId, mangledPointer)
                valueVal == GetVal(workGroupId, mangledValue)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, pointerVal, Index(-1)), Var(mangledPointer.scope, mangledPointer.name, pointerVal & valueVal, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, DynamicNodeSet, globalCounter, snapShotMap>>
OpBitcast(t, var, operand) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand == Mangle(t, operand)

    IN
        /\  LET operandVal == GetVal(workGroupId, mangledOperand)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, operandVal, Index(-1))})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state, DynamicNodeSet, globalCounter, snapShotMap>>

OpShiftLeftLogical(t, var, base, shift) == 
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledBase == Mangle(t, base)
        mangledShift == Mangle(t, shift)

    IN
        /\  LET baseVal == GetVal(workGroupId, mangledBase)
                shiftVal == GetVal(workGroupId, mangledShift)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, shiftL(baseVal, shiftVal), Index(-1))})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]   
        /\  UNCHANGED <<state, DynamicNodeSet, globalCounter, snapShotMap>>

OpShiftRightLogical(t, var, base, shift) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledBase == Mangle(t, base)
        mangledShift == Mangle(t, shift)

    IN
        /\  LET baseVal == GetVal(workGroupId, mangledBase)
                shiftVal == GetVal(workGroupId, mangledShift)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, shiftR(baseVal, shiftVal), Index(-1))})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state, DynamicNodeSet, globalCounter, snapShotMap>>

OpEqual(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                /\  IF operand1Val = operand2Val THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>


OpNotEqual(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                /\  IF operand1Val # operand2Val THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>


OpLess(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                /\  IF operand1Val < operand2Val THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>

OpLessOrEqual(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                /\  IF operand1Val <= operand2Val THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>

OpGreater(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                /\  IF operand1Val > operand2Val THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>

OpGreaterOrEqual(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                /\  IF operand1Val >= operand2Val THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>

OpBitwiseOr(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, operand1Val | operand2Val, Index(-1))})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]   
        /\  UNCHANGED <<state, DynamicNodeSet, globalCounter, snapShotMap>>     

OpBitwiseAnd(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, operand1Val & operand2Val, Index(-1))})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state, DynamicNodeSet, globalCounter, snapShotMap>>

OpAdd(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, operand1Val + operand2Val, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, DynamicNodeSet, globalCounter, snapShotMap>>


OpAtomicAdd(t, var, pointer, value) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledPointer == Mangle(t, pointer)
        mangledValue == Mangle(t, value)

    IN
        /\  LET pointerVal == GetVal(workGroupId, mangledPointer)
                valueVal == GetVal(workGroupId, mangledValue)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, pointerVal, Index(-1)), Var(mangledPointer.scope, mangledPointer.name, pointerVal + valueVal, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, DynamicNodeSet, globalCounter, snapShotMap>>

OpSub(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, operand1Val - operand2Val, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, DynamicNodeSet, globalCounter, snapShotMap>>

OpAtomicSub(t, var, pointer, value) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledPointer == Mangle(t, pointer)
        mangledValue == Mangle(t, value)

    IN
        /\  LET pointerVal == GetVal(workGroupId, mangledPointer)
                valueVal == GetVal(workGroupId, mangledValue)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, pointerVal, Index(-1)), Var(mangledPointer.scope, mangledPointer.name, pointerVal - valueVal, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, DynamicNodeSet, globalCounter, snapShotMap>>

OpMul(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, operand1Val * operand2Val, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, DynamicNodeSet, globalCounter, snapShotMap>>

OpMod(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, operand1Val % operand2Val, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, DynamicNodeSet, globalCounter, snapShotMap>>

GetGlobalId(t, result) ==
    LET mangledResult == Mangle(t, result)
    IN
        /\
            \/  
                /\  IsVariable(result)
                /\  VarExists(WorkGroupId(t)+1, result)
            \/  IsIntermediate(result)
        /\  Assignment(t, {Var(result.scope, result.name, GlobalInvocationId(t), Index(-1))})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state>>

OpAtomicLoadSync(t, result, pointer) ==
    LET mangledResult == Mangle(t, result)
        mangledPointer == Mangle(t, pointer)
        workGroupId == WorkGroupId(t) + 1
        sgIdx == SubgroupIndex(t)
        currentPc == pc[t]
        sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
        currentDB == CurrentDynamicNode(workGroupId, t)
        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
        aligned == unknown_subgroup_threads = {} /\ \A sthread \in active_subgroup_threads: pc[sthread] = currentPc
        pointerVar == GetVar(workGroupId, mangledPointer)
        assignmentSet ==
            IF IsIntermediate(mangledResult) THEN
                LET evaluatedIndex == EvalExpr(t, workGroupId, pointer.index)
                    value == IF evaluatedIndex > 0 THEN pointerVar.value[evaluatedIndex] ELSE pointerVar.value
                IN {Var(result.scope, Mangle(t, result).name, value, Index(-1))}
            ELSE
                LET resultVar == mangledResult
                    evaluatedPointerIndex == EvalExpr(t, workGroupId, pointer.index)
                    evaluatedResultIndex == EvalExpr(t, workGroupId, result.index)
                IN
                    IF evaluatedPointerIndex > 0 /\ evaluatedResultIndex > 0 THEN
                        {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value[evaluatedPointerIndex])}
                    ELSE IF evaluatedPointerIndex > 0 THEN
                        {Var(resultVar.scope, resultVar.name, pointerVar.value[evaluatedPointerIndex], resultVar.index)}
                    ELSE IF evaluatedResultIndex > 0 THEN
                        {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value)}
                    ELSE
                        {Var(resultVar.scope, resultVar.name, pointerVar.value, resultVar.index)}
        remaining == {sthread \in active_subgroup_threads : sthread # t /\ pc[sthread] = currentPc}
    IN
        /\ (IsVariable(mangledResult) \/ IsIntermediate(mangledResult))
        /\ IsVariable(mangledPointer)
        /\ VarExists(workGroupId, mangledPointer)
        /\ IF currentDB.sis[workGroupId][sgIdx][currentPc] = FALSE THEN
                IF ~aligned THEN
                    /\ state' = [state EXCEPT ![t] = "subgroup"]
                    /\ UNCHANGED <<pc, threadLocals, globalVars, DynamicNodeSet, globalCounter, snapShotMap>>
                ELSE
                    LET newDBSet == SetSISInDB(DynamicNodeSet, currentDB, workGroupId, sgIdx, currentPc, TRUE)
                    IN
                        /\ DynamicNodeSet' = newDBSet
                        /\ state' = StateUpdateSubgroup(workGroupId, active_subgroup_threads, newDBSet)
                        /\ UNCHANGED <<pc, threadLocals, globalVars, globalCounter, snapShotMap>>
           ELSE
                LET newDBSet == IF remaining = {}
                                 THEN SetSISInDB(DynamicNodeSet, currentDB, workGroupId, sgIdx, currentPc, FALSE)
                                 ELSE DynamicNodeSet
                IN
                    /\ Assignment(t, assignmentSet)
                    /\ pc' = [pc EXCEPT ![t] = pc[t] + 1]
                    /\ DynamicNodeSet' = newDBSet
                    /\ state' = [state EXCEPT ![t] = "ready"]
                    /\ UNCHANGED <<globalCounter, snapShotMap>>


\* It does not handle the situation where result is an index to array
OpAtomicLoad(t, result, pointer) ==
    LET mangledResult == Mangle(t, result)
        mangledPointer == Mangle(t, pointer)
    IN
        /\
            \/  
                /\  IsVariable(mangledResult)
                \* /\  VarExists(WorkGroupId(t)+1, mangledResult)
            \/  IsIntermediate(mangledResult)
        /\  IsVariable(mangledPointer)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer)
        /\  IF IsIntermediate(mangledResult) THEN 
                LET pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
                    evaluatedIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
                IN 
                    /\
                        IF evaluatedIndex > 0 THEN 
                            Assignment(t, {Var(mangledResult.scope, mangledResult.name, pointerVar.value[evaluatedIndex], Index(-1))})
                        ELSE
                            Assignment(t, {Var(mangledResult.scope, mangledResult.name, pointerVar.value, Index(-1))})
            ELSE
                LET pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
                    \* resultVar == GetVar(WorkGroupId(t)+1, mangledResult)
                    resultVar == mangledResult
                    evaluatedPointerIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
                    evaluatedResultIndex == EvalExpr(t, WorkGroupId(t)+1, result.index)
                IN
                    /\
                        IF evaluatedPointerIndex > 0 /\ evaluatedResultIndex > 0 THEN
                            Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value[evaluatedPointerIndex])})
                        ELSE IF evaluatedPointerIndex > 0 THEN
                            Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value[evaluatedPointerIndex], Index(-1))})
                        ELSE IF evaluatedResultIndex > 0 THEN
                            Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value)})
                        ELSE
                            Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value, Index(-1))})  
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state, DynamicNodeSet, globalCounter, snapShotMap>>

OpAtomicLoadCollective(t, result, pointer) ==
    LET mangledResult == Mangle(t, result)
        mangledPointer == Mangle(t, pointer)
    IN
        /\
            \/  
                /\  IsVariable(mangledResult)
                \* /\  VarExists(WorkGroupId(t)+1, mangledResult)
            \/  IsIntermediate(mangledResult)
        /\  IsVariable(mangledPointer)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer)
        /\  IF IsIntermediate(mangledResult) THEN 
                LET workGroupId == WorkGroupId(t) + 1
                    sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
                    currentDB == CurrentDynamicNode(workGroupId, t)
                    active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
                    unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
                    pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
                    evaluatedIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
                IN 
                    /\
                        IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
                            /\  state' = [state EXCEPT ![t] = "subgroup"]
                            /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                        ELSE
                            /\  LET loadVars == {
                                    IF evaluatedIndex > 0 THEN 
                                        Var(result.scope, Mangle(sthread, result).name, pointerVar.value[evaluatedIndex], Index(-1))
                                    ELSE
                                        Var(result.scope, Mangle(sthread, result).name, pointerVar.value, Index(-1))
                                    : sthread \in active_subgroup_threads
                                }
                                IN Assignment(t, loadVars)
                            /\  state' = [
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            "ready" 
                                        ELSE 
                                            state[tid]
                                ]
                            /\  pc' = [
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            pc[tid] + 1
                                        ELSE 
                                            pc[tid]
                                ]
                            /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
            ELSE
                LET workGroupId == WorkGroupId(t) + 1
                    sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
                    currentDB == CurrentDynamicNode(workGroupId, t)
                    active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
                    unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
                    pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
                IN
                    /\
                        IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
                            /\  state' = [state EXCEPT ![t] = "subgroup"]
                            /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                        ELSE
                            /\  LET loadVars == {
                                    LET resultVar == Mangle(sthread, result)
                                        evaluatedPointerIndex == EvalExpr(sthread, WorkGroupId(sthread)+1, pointer.index)
                                        evaluatedResultIndex == EvalExpr(sthread, WorkGroupId(sthread)+1, result.index)
                                    IN
                                        IF evaluatedPointerIndex > 0 /\ evaluatedResultIndex > 0 THEN
                                            ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value[evaluatedPointerIndex])
                                        ELSE IF evaluatedPointerIndex > 0 THEN
                                            Var(resultVar.scope, resultVar.name, pointerVar.value[evaluatedPointerIndex], Index(-1))
                                        ELSE IF evaluatedResultIndex > 0 THEN
                                            ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value)
                                        ELSE
                                            Var(resultVar.scope, resultVar.name, pointerVar.value, Index(-1))
                                    : sthread \in active_subgroup_threads
                                }
                                IN Assignment(t, loadVars)
                            /\  state' = [
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            "ready" 
                                        ELSE 
                                            state[tid]
                                ]
                            /\  pc' = [
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            pc[tid] + 1
                                        ELSE 
                                            pc[tid]
                                ]
                            /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>

OpAtomicStoreSync(t, pointer, value) == 
    LET mangledPointer == Mangle(t, pointer)
        workGroupId == WorkGroupId(t) + 1
        sgIdx == SubgroupIndex(t)
        currentPc == pc[t]
        sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
        currentDB == CurrentDynamicNode(workGroupId, t)
        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
        aligned == unknown_subgroup_threads = {} /\ \A sthread \in active_subgroup_threads: pc[sthread] = currentPc
        pointerVar == GetVar(workGroupId, mangledPointer)
        evaluatedPointerIndex == EvalExpr(t, workGroupId, pointer.index)
        valueToStore == EvalExpr(t, workGroupId, value)
        assignmentSet ==
            IF evaluatedPointerIndex > 0 THEN
                {ChangeElementAt(pointerVar, evaluatedPointerIndex, valueToStore)}
            ELSE
                {Var(pointerVar.scope, pointerVar.name, valueToStore, pointerVar.index)}
        remaining == {sthread \in active_subgroup_threads : sthread # t /\ pc[sthread] = currentPc}
    IN
        /\ IsVariable(mangledPointer)
        /\ VarExists(workGroupId, mangledPointer)
        /\ IF currentDB.sis[workGroupId][sgIdx][currentPc] = FALSE THEN
                IF ~aligned THEN
                    /\ state' = [state EXCEPT ![t] = "subgroup"]
                    /\ UNCHANGED <<pc, threadLocals, globalVars, DynamicNodeSet, globalCounter, snapShotMap>>
                ELSE
                    LET newDBSet == SetSISInDB(DynamicNodeSet, currentDB, workGroupId, sgIdx, currentPc, TRUE)
                    IN
                        /\ DynamicNodeSet' = newDBSet
                        /\ state' = StateUpdateSubgroup(workGroupId, active_subgroup_threads, newDBSet)
                        /\ UNCHANGED <<pc, threadLocals, globalVars, globalCounter, snapShotMap>>
           ELSE
                LET newDBSet == IF remaining = {}
                                 THEN SetSISInDB(DynamicNodeSet, currentDB, workGroupId, sgIdx, currentPc, FALSE)
                                 ELSE DynamicNodeSet
                IN
                    /\ Assignment(t, assignmentSet)
                    /\ pc' = [pc EXCEPT ![t] = pc[t] + 1]
                    /\ DynamicNodeSet' = newDBSet
                    /\ state' = [state EXCEPT ![t] = "ready"]
                    /\ UNCHANGED <<globalCounter, snapShotMap>>


OpAtomicStore(t, pointer, value) == 
    LET mangledPointer == Mangle(t, pointer)
    IN
        /\  IsVariable(mangledPointer)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer)
        /\  LET pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
                evaluatedPointerIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
            IN
                /\
                    IF evaluatedPointerIndex > 0 THEN 
                        Assignment(t, {ChangeElementAt(pointerVar, evaluatedPointerIndex, EvalExpr(t, WorkGroupId(t)+1, value))})
                    ELSE
                        Assignment(t, {Var(pointerVar.scope, pointerVar.name, EvalExpr(t, WorkGroupId(t)+1, value), pointerVar.index)})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state,  DynamicNodeSet, globalCounter, snapShotMap>>

OpAtomicStoreCollective(t, pointer, value) == 
    LET mangledPointer == Mangle(t, pointer)
    IN
        /\  IsVariable(mangledPointer)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer)
        /\  LET pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
                evaluatedPointerIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
                workGroupId == WorkGroupId(t) + 1
                sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
                currentDB == CurrentDynamicNode(workGroupId, t)
                active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
                unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
            IN 
                IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
                    /\  state' = [state EXCEPT ![t] = "subgroup"]
                    /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                ELSE
                    /\  LET storeVars == {
                            IF evaluatedPointerIndex > 0 THEN 
                                ChangeElementAt(GetVar(WorkGroupId(sthread)+1, Mangle(sthread, pointer)), evaluatedPointerIndex, EvalExpr(sthread, WorkGroupId(sthread)+1, value))
                            ELSE
                                Var(pointerVar.scope, Mangle(sthread, pointer).name, EvalExpr(sthread, WorkGroupId(sthread)+1, value), pointerVar.index)
                            : sthread \in active_subgroup_threads
                        }
                        IN Assignment(t, storeVars)
                    /\  state' = [
                            tid \in Threads |->
                                IF tid \in active_subgroup_threads THEN 
                                    "ready" 
                                ELSE 
                                    state[tid]
                        ]
                    /\  pc' = [
                            tid \in Threads |->
                                IF tid \in active_subgroup_threads THEN 
                                    pc[tid] + 1
                                ELSE 
                                    pc[tid]
                        ]
        /\  UNCHANGED <<DynamicNodeSet, globalCounter, snapShotMap>>

OpAtomicIncrement(t, pointer) == 
    LET mangledPointer == Mangle(t, pointer)
    IN
        /\  IsVariable(mangledPointer)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer)
        /\  IsArray(pointer) = FALSE
        /\  LET pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
                evaluatedPointerIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
            IN
                /\
                    IF evaluatedPointerIndex > 0 THEN 
                        Assignment(t, {ChangeElementAt(pointerVar, evaluatedPointerIndex, pointerVar.value[evaluatedPointerIndex] + 1)})
                    ELSE  
                        Assignment(t, {Var(pointerVar.scope, pointerVar.name, pointerVar.value + 1, pointerVar.index)})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state,  DynamicNodeSet, globalCounter, snapShotMap>>


OpAtomicDecrement(t, pointer) == 
    LET mangledPointer == Mangle(t, pointer)
    IN
        /\  IsVariable(mangledPointer)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer)
        /\  LET pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
                evaluatedPointerIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
            IN
                /\
                    IF evaluatedPointerIndex > 0 THEN 
                        Assignment(t, {ChangeElementAt(pointerVar, evaluatedPointerIndex, pointerVar.value[evaluatedPointerIndex] - 1)})
                    ELSE  
                        Assignment(t, {Var(pointerVar.scope, pointerVar.name, pointerVar.value - 1, pointerVar.index)})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state,  DynamicNodeSet, globalCounter, snapShotMap>>


OpControlBarrier(t, scope) ==
    IF GetVal(-1, scope) = "subgroup" THEN \* already waiting at a subgroup barrier
        \* find all threads and their corresponding barrier state within the same subgroup
        LET sthreads == ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t))
            workGroupId == WorkGroupId(t)+1
            currentDB == CurrentDynamicNode(workGroupId, t)
            active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
            unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
            not_executing_subgroup_threads == currentDB.notExecuteSet[workGroupId] \intersect sthreads
        IN
            IF not_executing_subgroup_threads # {} THEN 
                Print("UB: All threads within subgroup must converge at current block", FALSE)
            \* if there exists thread in the subgroup that has not reached the subgroup barrier, set the barrier to current thread
            ELSE IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
                /\  state' = [state EXCEPT ![t] = "subgroup"]
                /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
            \* if all threads in the subgroup are waiting at the barrier, release them
            ELSE 
                \* release all barrier in the subgroup, marking state as ready
                /\  state' = [
                        tid \in Threads |->
                            IF tid \in sthreads THEN 
                                "ready" 
                            ELSE 
                                state[tid]
                    ]
                \* increment the program counter for all threads in the subgroup
                /\  pc' = [
                        tid \in Threads |->
                            IF tid \in sthreads THEN 
                                pc[tid] + 1
                            ELSE 
                                pc[tid]
                    ]
                /\  UNCHANGED <<threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>

    ELSE IF GetVal(-1, scope) = "workgroup" THEN \* already waiting at a workgroup barrier
        LET workGroupId == WorkGroupId(t)+1
            currentDB == CurrentDynamicNode(workGroupId, t)
            wthreads == ThreadsWithinWorkGroup(WorkGroupId(t))
            active_workgroup_threads == currentDB.currentThreadSet[workGroupId]
            unknown_workgroup_threads == currentDB.unknownSet[workGroupId]
            not_executing_workgroup_threads == currentDB.notExecuteSet[workGroupId]
        IN
            IF not_executing_workgroup_threads # {} THEN 
                Print("UB: All threads within workgroup must converge at current block", FALSE)
            \* if there exists thread in the subgroup that has not reached the workgroup barrier, set the barrier to current thread
            ELSE IF unknown_workgroup_threads # {}  \/ \E wthread \in wthreads: pc[wthread] # pc[t] THEN
                /\  state' = [state EXCEPT ![t] = "workgroup"]
                /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
            \* if all threads in the subgroup are waiting at the barrier, release them
            ELSE 
                \* release all barrier in the subgroup, marking state as ready
                /\  state' = [
                        tid \in Threads |->
                            IF tid \in wthreads THEN 
                                "ready" 
                            ELSE 
                                state[tid]
                    ]
                \* increment the program counter for all threads in the subgroup
                /\  pc' = [
                        tid \in Threads |->
                            IF tid \in wthreads THEN 
                                pc[tid] + 1
                            ELSE 
                                pc[tid]
                    ]
                /\  UNCHANGED <<threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
    ELSE    
        FALSE



OpGroupAll(t, result, scope, predicate) ==
    LET mangledResult == Mangle(t, result)
    IN
        /\  
            \/  /\  IsVariable(mangledResult)
            \/  IsIntermediate(mangledResult)
        /\  scope.value \in ScopeOperand
        /\  IF scope.value = "subgroup" THEN
                /\  LET sthreads == ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t))
                        workGroupId == WorkGroupId(t)+1
                        currentDB == CurrentDynamicNode(workGroupId, t)
                        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
                        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
                        not_executing_subgroup_threads == currentDB.notExecuteSet[workGroupId] \intersect sthreads
                    IN
                        IF not_executing_subgroup_threads # {} THEN 
                                Print("UB: All threads within subgroup must converge at current block for OpGroupAll", FALSE)
                        \* if there exists thread in the subgroup that has not reached the opgroupAll, set the barrier to current thread
                        ELSE IF unknown_subgroup_threads # {} \/ \E sthread \in sthreads: pc[sthread] # pc[t] THEN
                            /\  state' = [state EXCEPT ![t] = "subgroup"]
                            /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                        ELSE IF \A sthread \in sthreads: EvalExpr(sthread, workGroupId, predicate) = TRUE THEN 
                            /\  Assignment(t, {Var(mangledResult.scope, Mangle(sthread, result).name, TRUE, Index(-1)): sthread \in sthreads})
                            /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
                                    tid \in Threads |->
                                        IF tid \in sthreads THEN 
                                            "ready" 
                                        ELSE 
                                            state[tid]
                                ]
                            /\  pc' = [
                                    tid \in Threads |->
                                        IF tid \in sthreads THEN 
                                            pc[tid] + 1
                                        ELSE 
                                            pc[tid]
                                ]
                            /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                        ELSE 
                            /\  Assignment(t, {Var(mangledResult.scope, Mangle(sthread, result).name, FALSE, Index(-1)): sthread \in sthreads })
                            /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
                                    tid \in Threads |->
                                        IF tid \in sthreads THEN 
                                            "ready" 
                                        ELSE 
                                            state[tid]
                                ]
                            /\  pc' = [
                                    tid \in Threads |->
                                        IF tid \in sthreads THEN 
                                            pc[tid] + 1
                                        ELSE 
                                            pc[tid]
                                ]
                            /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
            ELSE IF scope.value = "workgroup" THEN 
                /\ LET  workGroupId == WorkGroupId(t)+1
                        currentDB == CurrentDynamicNode(workGroupId, t)
                        wthreads == ThreadsWithinWorkGroup(WorkGroupId(t))
                        active_workgroup_threads == currentDB.currentThreadSet[workGroupId]
                        unknown_workgroup_threads == currentDB.unknownSet[workGroupId]
                        not_executing_workgroup_threads == currentDB.notExecuteSet[workGroupId]
                    IN
                        IF not_executing_workgroup_threads # {} THEN 
                            Print("UB: All threads within workgroup must converge at current block", FALSE)
                        \* if there exists thread in the subgroup that has not reached the workgroup barrier, set the barrier to current thread
                        ELSE IF unknown_workgroup_threads # {}  \/ \E wthread \in wthreads: pc[wthread] # pc[t] THEN
                                /\  state' = [state EXCEPT ![t] = "workgroup"]
                                /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                        ELSE IF \A wthread \in wthreads: EvalExpr(wthread, workGroupId, predicate) = TRUE THEN 
                            /\  Assignment(t, {Var(mangledResult.scope, Mangle(wthread, result).name, TRUE, Index(-1)): wthread \in wthreads})
                            /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
                                    tid \in Threads |->
                                        IF tid \in wthreads THEN 
                                            "ready" 
                                        ELSE 
                                            state[tid]
                                ]
                            /\  pc' = [
                                    tid \in Threads |->
                                        IF tid \in wthreads THEN 
                                            pc[tid] + 1
                                        ELSE 
                                            pc[tid]
                                ]
                            /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                        ELSE 
                            /\  Assignment(t, {Var(mangledResult.scope, Mangle(wthread, result).name, FALSE, Index(-1)): wthread \in wthreads })
                            /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
                                    tid \in Threads |->
                                        IF tid \in wthreads THEN 
                                            "ready" 
                                        ELSE 
                                            state[tid]
                                ]
                            /\  pc' = [
                                    tid \in Threads |->
                                        IF tid \in wthreads THEN 
                                            pc[tid] + 1
                                        ELSE 
                                            pc[tid]
                                ]
                            /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
            ELSE
                /\  FALSE

OpGroupAny(t, result, scope, predicate) ==
    LET mangledResult == Mangle(t, result)
    IN
        /\  
            \/  /\  IsVariable(mangledResult)
                \* /\  VarExists(WorkGroupId(t)+1, mangledResult)
            \/  IsIntermediate(mangledResult)
        /\  scope.value \in ScopeOperand
        /\  IF scope.value = "subgroup" THEN
                /\  LET sthreads == ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t))
                        workGroupId == WorkGroupId(t)+1
                        currentDB == CurrentDynamicNode(workGroupId, t)
                        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
                        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
                        not_executing_subgroup_threads == currentDB.notExecuteSet[workGroupId] \intersect sthreads
                    IN
                        IF not_executing_subgroup_threads # {} THEN 
                                Print("UB: All threads within subgroup must converge at current block for OpGroupAny", FALSE)
                        \* if there exists thread in the subgroup that has not reached the opgroupAll, set the barrier to current thread
                        ELSE IF unknown_subgroup_threads # {} \/ \E sthread \in sthreads: pc[sthread] # pc[t] THEN
                            /\  state' = [state EXCEPT ![t] = "subgroup"]
                            /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                        ELSE IF \E sthread \in sthreads: EvalExpr(sthread, workGroupId, predicate) = TRUE THEN 
                            /\  Assignment(t, {Var(mangledResult.scope, Mangle(sthread, result).name, TRUE, Index(-1)): sthread \in sthreads})
                            /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
                                    tid \in Threads |->
                                        IF tid \in sthreads THEN 
                                            "ready" 
                                        ELSE 
                                            state[tid]
                                ]
                            /\  pc' = [
                                    tid \in Threads |->
                                        IF tid \in sthreads THEN 
                                            pc[tid] + 1
                                        ELSE 
                                            pc[tid]
                                ]
                            /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                        ELSE 
                            /\  Assignment(t, {Var(mangledResult.scope, Mangle(sthread, result).name, FALSE, Index(-1)): sthread \in sthreads })
                            /\  state' = [\* release all barrier in the subgroup, marking barrier as
                                    tid \in Threads |->
                                        IF tid \in sthreads THEN 
                                            "ready" 
                                        ELSE 
                                            state[tid]
                                ]
                            /\  pc' = [
                                    tid \in Threads |->
                                        IF tid \in sthreads THEN 
                                            pc[tid] + 1
                                        ELSE 
                                            pc[tid]
                                ]
                            /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
            ELSE IF scope.value = "workgroup" THEN
                /\ LET  workGroupId == WorkGroupId(t)+1
                        currentDB == CurrentDynamicNode(workGroupId, t)
                        wthreads == ThreadsWithinWorkGroup(WorkGroupId(t))
                        active_workgroup_threads == currentDB.currentThreadSet[workGroupId]
                        unknown_workgroup_threads == currentDB.unknownSet[workGroupId]
                        not_executing_workgroup_threads == currentDB.notExecuteSet[workGroupId]
                    IN
                        IF not_executing_workgroup_threads # {} THEN 
                            Print("UB: All threads within workgroup must converge at current block", FALSE)
                        \* if there exists thread in the subgroup that has not reached the workgroup barrier, set the barrier to current thread
                        ELSE IF unknown_workgroup_threads # {}  \/ \E wthread \in wthreads: pc[wthread] # pc[t] THEN
                                /\  state' = [state EXCEPT ![t] = "workgroup"]
                                /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                        ELSE IF \E wthread \in wthreads: EvalExpr(wthread, workGroupId, predicate) = TRUE THEN 
                            /\  Assignment(t, {Var(mangledResult.scope, Mangle(wthread, result).name, TRUE, Index(-1)): wthread \in wthreads})
                            /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
                                    tid \in Threads |->
                                        IF tid \in wthreads THEN 
                                            "ready" 
                                        ELSE 
                                            state[tid]
                                ]
                            /\  pc' = [
                                    tid \in Threads |->
                                        IF tid \in wthreads THEN 
                                            pc[tid] + 1
                                        ELSE 
                                            pc[tid]
                                ]
                            /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                        ELSE 
                            /\  Assignment(t, {Var(mangledResult.scope, Mangle(wthread, result).name, FALSE, Index(-1)): wthread \in wthreads })
                            /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
                                    tid \in Threads |->
                                        IF tid \in wthreads THEN 
                                            "ready" 
                                        ELSE 
                                            state[tid]
                                ]
                            /\  pc' = [
                                    tid \in Threads |->
                                        IF tid \in wthreads THEN 
                                            pc[tid] + 1
                                        ELSE 
                                            pc[tid]
                                ]
                            /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
            ELSE
                /\  FALSE

OpGroupNonUniformAll(t, result, scope, predicate) ==
    LET mangledResult == Mangle(t, result)
    IN
        /\  
            \/  /\  IsVariable(result)
            \/  IsIntermediate(result)
        /\  scope.value \in ScopeOperand
        /\  IF scope.value = "subgroup" THEN
                /\  LET workGroupId == WorkGroupId(t) + 1
                        sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
                        currentDB == CurrentDynamicNode(workGroupId, t)
                        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
                        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
                    IN
                        \* if there are threads in tangle not reaching the instruction point,
                        \* or there are threads in unknown set, make current thread waiting
                        IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
                            /\  state' = [state EXCEPT ![t] = "subgroup"]
                            /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                        ELSE IF \A sthread \in active_subgroup_threads: EvalExpr(sthread, workGroupId, predicate) = TRUE THEN 
                            /\  Assignment(t, {Var(result.scope, Mangle(sthread, result).name, TRUE, Index(-1)): sthread \in active_subgroup_threads})
                            /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            "ready" 
                                        ELSE 
                                            state[tid]
                                ]
                            /\  pc' = [
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            pc[tid] + 1
                                        ELSE 
                                            pc[tid]
                                ]
                            /\ UNCHANGED <<globalVars, globalCounter, DynamicNodeSet, snapShotMap>>
                        ELSE 
                            /\  Assignment(t, {Var(result.scope, Mangle(sthread, result).name, FALSE, Index(-1)): sthread \in active_subgroup_threads })
                            /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            "ready" 
                                        ELSE 
                                            state[tid]
                                ]
                            /\  pc' = [
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            pc[tid] + 1
                                        ELSE 
                                            pc[tid]
                                ]
                            /\ UNCHANGED <<globalVars, globalCounter, DynamicNodeSet, snapShotMap>>
            ELSE
                /\  FALSE

OpGroupNonUniformAllEqual(t, result, scope, value) ==
    LET mangledResult == Mangle(t, result)
    IN
        /\  
            \/  /\  IsVariable(result)
            \/  IsIntermediate(result)
        /\  scope.value \in ScopeOperand
        /\  IF scope.value = "subgroup" THEN
                /\  LET workGroupId == WorkGroupId(t) + 1
                        sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
                        currentDB == CurrentDynamicNode(workGroupId, t)
                        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
                        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
                        equalVal == EvalExpr(t, workGroupId, value)
                    IN
                        \* if there are threads in tangle not reaching the instruction point,
                        \* or there are threads in unknown set, make current thread waiting
                        IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
                            /\  state' = [state EXCEPT ![t] = "subgroup"]
                            /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                        ELSE IF \A sthread \in active_subgroup_threads: EvalExpr(sthread, workGroupId, value) = equalVal THEN 
                            /\  Assignment(t, {Var(result.scope, Mangle(sthread, result).name, TRUE, Index(-1)): sthread \in active_subgroup_threads})
                            /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            "ready" 
                                        ELSE 
                                            state[tid]
                                ]
                            /\  pc' = [
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            pc[tid] + 1
                                        ELSE 
                                            pc[tid]
                                ]
                            /\ UNCHANGED <<globalVars, globalCounter, DynamicNodeSet, snapShotMap>>
                        ELSE 
                            /\  Assignment(t, {Var(result.scope, Mangle(sthread, result).name, FALSE, Index(-1)): sthread \in active_subgroup_threads })
                            /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            "ready" 
                                        ELSE 
                                            state[tid]
                                ]
                            /\  pc' = [
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            pc[tid] + 1
                                        ELSE 
                                            pc[tid]
                                ]
                            /\ UNCHANGED <<globalVars, globalCounter, DynamicNodeSet, snapShotMap>>
            ELSE
                /\  FALSE

OpGroupNonUniformAny(t, result, scope, predicate) ==
    LET mangledResult == Mangle(t, result)
    IN
        /\  
            \/  /\  IsVariable(result)
            \/  IsIntermediate(result)
        /\  scope.value \in ScopeOperand
        /\  IF scope.value = "subgroup" THEN
                /\  LET workGroupId == WorkGroupId(t) + 1
                        sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
                        currentDB == CurrentDynamicNode(workGroupId, t)
                        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
                        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
                    IN
                        IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
                            /\  state' = [state EXCEPT ![t] = "subgroup"]
                            /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                        ELSE IF \E sthread \in active_subgroup_threads: EvalExpr(sthread, workGroupId, predicate) = TRUE THEN 
                            /\  Assignment(t, {Var(result.scope, Mangle(sthread, result).name, TRUE, Index(-1)): sthread \in active_subgroup_threads})
                            /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            "ready" 
                                        ELSE 
                                            state[tid]
                                ]
                            /\  pc' = [
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            pc[tid] + 1
                                        ELSE 
                                            pc[tid]
                                ]
                            /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                        ELSE 
                            /\  Assignment(t, {Var(result.scope, Mangle(sthread, result).name, FALSE, Index(-1)): sthread \in active_subgroup_threads })
                            /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            "ready" 
                                        ELSE 
                                            state[tid]
                                ]
                            /\  pc' = [
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            pc[tid] + 1
                                        ELSE 
                                            pc[tid]
                                ]
                            /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
            ELSE
                /\  FALSE

OpGroupNonUniformBroadcast(t, result, scope, value, id) ==
    LET mangledResult == Mangle(t, result)
    IN
        /\  scope.value \in ScopeOperand
        /\  IF scope.value = "subgroup" THEN
                /\  LET workGroupId == WorkGroupId(t) + 1
                        sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
                        currentDB == CurrentDynamicNode(workGroupId, t)
                        tidVal == EvalExpr(t, workGroupId, id) + 1
                        gtidVal == tidVal + SubgroupId(t) * SubgroupSize + WorkGroupId(t) * WorkGroupSize
                        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
                        not_excecuteing_subgroup_threads == currentDB.notExecuteSet[workGroupId] \intersect sthreads
                        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
                    IN
                        \*  resulting value is undefined if Id is not part of the scope restricted tangle, or is greater than or equal to the size of the scope.
                        IF (tidVal > SubgroupSize) \/ (gtidVal \in not_excecuteing_subgroup_threads) THEN
                            Print("UB: Id is not part of the scope restricted tangle, or is greater than or equal to the size of the scope.", FALSE)
                        ELSE IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
                            /\  state' = [state EXCEPT ![t] = "subgroup"]
                            /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                        \*  behavior is undefined when Id is not dynamically uniform
                        ELSE IF \E sthread \in sthreads: (EvalExpr(sthread, workGroupId, id) + 1) # tidVal THEN 
                            Print("UB: Id is not dynamically uniform", FALSE)
                        ELSE 
                            /\  Assignment(t, {Var(result.scope, Mangle(sthread, result).name, EvalExpr(gtidVal, WorkGroupId(gtidVal) + 1, value), Index(-1)): sthread \in active_subgroup_threads })
                            /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            "ready" 
                                        ELSE 
                                            state[tid]
                                ]
                            /\  pc' = [
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            pc[tid] + 1
                                        ELSE 
                                            pc[tid]
                                ]
                            /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
            ELSE
                /\  FALSE

(* result and pointer are variable *)
OpAtomicExchange(t, result, pointer, value) ==
    LET mangledResult == Mangle(t, result)
        mangledPointer == Mangle(t, pointer)
    IN
        /\  IsVariable(mangledResult)
        \* /\  VarExists(WorkGroupId(t)+1, mangledResult)
        /\  IsVariable(mangledPointer)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer)

        /\  LET pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
                \* resultVar == GetVar(WorkGroupId(t)+1, mangledResult)
                resultVar == mangledResult
                evaluatedResultIndex == EvalExpr(t, WorkGroupId(t)+1, result.index)
                evaluatedPointerIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
                evaluatedValue == EvalExpr(t, WorkGroupId(t)+1, value)
            IN
                IF evaluatedResultIndex > 0 /\ evaluatedPointerIndex > 0 THEN
                    Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value[evaluatedPointerIndex]), ChangeElementAt(pointerVar, evaluatedPointerIndex, evaluatedValue)})
                ELSE IF evaluatedResultIndex > 0 THEN
                    Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value), Var(pointerVar.scope, pointerVar.name, evaluatedValue, pointerVar.index)})
                ELSE IF evaluatedPointerIndex > 0 THEN
                    Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value[evaluatedPointerIndex], resultVar.index), ChangeElementAt(pointerVar, evaluatedPointerIndex, evaluatedValue)})
                ELSE
                    Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value, resultVar.index), Var(pointerVar.scope, pointerVar.name, evaluatedValue, pointerVar.index)})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state,  DynamicNodeSet, globalCounter, snapShotMap>>

(* result and pointer are variable, compare and value are literal *)
OpAtomicCompareExchange(t, result, pointer, value, comparator) ==
    LET mangledResult == Mangle(t, result)
        mangledPointer == Mangle(t, pointer)
    IN
        /\  IsVariable(mangledResult)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer)

        /\  LET pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
                \* resultVar == GetVar(WorkGroupId(t)+1, result)
                resultVar == mangledResult
                evaluatedPointerIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
                evaluatedResultIndex == EvalExpr(t, WorkGroupId(t)+1, result.index)
                evaluatedValue == EvalExpr(t, WorkGroupId(t)+1, value)
                evaluatedComparator == EvalExpr(t, WorkGroupId(t)+1, comparator)
            IN 
                IF pointerVar.value = evaluatedComparator THEN
                    /\  
                        IF evaluatedResultIndex > 0 /\ evaluatedPointerIndex > 0 THEN
                            Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value[evaluatedPointerIndex]), ChangeElementAt(pointerVar, evaluatedPointerIndex, evaluatedValue)})
                        ELSE IF evaluatedResultIndex > 0 THEN
                            Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value), Var(pointerVar.scope, pointerVar.name, evaluatedValue, pointerVar.index)})
                        ELSE IF evaluatedPointerIndex > 0 THEN
                            Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value[evaluatedPointerIndex], resultVar.index), ChangeElementAt(pointerVar, evaluatedPointerIndex, evaluatedValue)})
                        ELSE
                            Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value, resultVar.index), Var(pointerVar.scope, pointerVar.name, evaluatedValue, pointerVar.index)})

                ELSE
                    /\
                        IF evaluatedResultIndex > 0 /\ evaluatedPointerIndex > 0 THEN
                            Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value[evaluatedPointerIndex])})
                        ELSE IF evaluatedResultIndex > 0 THEN
                            Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value)})
                        ELSE IF evaluatedPointerIndex > 0 THEN
                            Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value[evaluatedPointerIndex], resultVar.index)})
                        ELSE
                            Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value, resultVar.index)})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state,  DynamicNodeSet, globalCounter, snapShotMap>>


OpBranchSync(t, label) == 
/\  LET workGroupId == WorkGroupId(t) + 1
        sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
        currentDB == CurrentDynamicNode(workGroupId, t)
        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
    IN
        \* if there are threads in tangle not reaching the instruction point,
        \* or there are threads in unknown set, make current thread waiting
        IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
            /\  state' = [state EXCEPT ![t] = "subgroup"]
            /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
        ELSE 
            /\  LET labelVal == GetVal(-1, label)
                    \* Update program counter for all active subgroup threads instead of just thread t
                    newPc == [thread \in Threads |-> 
                        IF thread \in active_subgroup_threads THEN 
                            GetVal(-1, label) 
                        ELSE 
                            pc[thread]]
                IN
                    LET counterNewDBSet == BranchConditionalUpdateSubgroup(workGroupId, active_subgroup_threads, pc[t], {labelVal}, active_subgroup_threads, {}, labelVal, -1)
                        newCounter == counterNewDBSet[1]
                        newDBSet == counterNewDBSet[2]
                        newState == StateUpdateSubgroup(workGroupId, active_subgroup_threads, newDBSet)
                        newSnapShotMap == SnapShotUpdateSubgroup(newDBSet, newState, active_subgroup_threads, newPc, newCounter)
                        matchedSnapShot == MeaningfulUpdate(newPc, newState, snapShotMap, newDBSet)
                    IN 
                        IF matchedSnapShot = {} THEN
                            /\  snapShotMap' = newSnapShotMap
                            /\  state' = newState
                            /\  DynamicNodeSet' = newDBSet 
                            /\  pc' = newPc
                            /\  globalCounter' = newCounter
                        ELSE
                            LET previousState == CHOOSE db \in matchedSnapShot: TRUE
                            IN
                                /\ state' = previousState.state
                                /\ DynamicNodeSet' = previousState.dynamicNodeSet
                                /\ globalCounter' = previousState.globalCounter
                                /\ pc' = previousState.pc
                                /\ UNCHANGED  <<threadLocals, globalVars, snapShotMap>>
            /\  UNCHANGED <<threadLocals, globalVars>>

OpBranch(t, label) ==
    /\  LET labelVal == GetVal(-1, label)
            workGroupId == WorkGroupId(t)+1
            newPc == [pc EXCEPT ![t] = GetVal(-1, label)]
        IN
            LET counterNewDBSet == BranchUpdate(workGroupId, t, pc[t], {labelVal}, labelVal, {labelVal})
                newCounter == counterNewDBSet[1]
                newDBSet == counterNewDBSet[2]
                newState == StateUpdate(workGroupId, t, newDBSet)
                newSnapShotMap == SnapShotUpdate(newDBSet, newState, t, newPc, newCounter)
                matchedSnapShot == MeaningfulUpdate(newPc, newState, snapShotMap, newDBSet)
            IN 
                IF matchedSnapShot = {} THEN
                    /\  snapShotMap' = newSnapShotMap
                    /\  state' = newState
                    /\  DynamicNodeSet' = newDBSet 
                    /\  pc' = newPc
                    /\  globalCounter' = newCounter
                ELSE
                    LET previousState == CHOOSE db \in matchedSnapShot: TRUE
                    IN
                        /\ state' = previousState.state
                        /\ DynamicNodeSet' = previousState.dynamicNodeSet
                        /\ globalCounter' = previousState.globalCounter
                        /\ pc' = previousState.pc
                        /\ UNCHANGED  <<threadLocals, globalVars, snapShotMap>>
    /\  UNCHANGED <<threadLocals, globalVars>>


OpBranchConditionalSync(t, condition, trueLabel, falseLabel) == 
    /\  IsLiteral(trueLabel)
    /\  IsLiteral(falseLabel)
    /\  LET workGroupId == WorkGroupId(t) + 1
                        sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
                        currentDB == CurrentDynamicNode(workGroupId, t)
                        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
                        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
        IN
            \* if there are threads in tangle not reaching the instruction point,
            \* or there are threads in unknown set, make current thread waiting
            IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
                /\  state' = [state EXCEPT ![t] = "subgroup"]
                /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
            ELSE 
                /\  LET trueLabelVal == GetVal(-1, trueLabel)
                        falseLabelVal == GetVal(-1, falseLabel)
                        \* Evaluate condition for each thread in the active subgroup
                        trueThreads == {thread \in active_subgroup_threads : EvalExpr(thread, WorkGroupId(thread)+1, condition) = TRUE}
                        falseThreads == active_subgroup_threads \ trueThreads
                        newPc == [thread \in Threads |-> 
                            IF thread \in trueThreads THEN 
                                trueLabelVal
                            ELSE IF thread \in falseThreads THEN 
                                falseLabelVal
                            ELSE 
                                pc[thread]]
                    IN
                        LET counterNewDBSet == BranchConditionalUpdateSubgroup(workGroupId, active_subgroup_threads, pc[t], {trueLabelVal, falseLabelVal}, trueThreads, falseThreads, trueLabelVal, falseLabelVal)
                            newCounter == counterNewDBSet[1]
                            newDBSet == counterNewDBSet[2]
                            newState == StateUpdateSubgroup(workGroupId, active_subgroup_threads, newDBSet)
                            newSnapShotMap == SnapShotUpdateSubgroup(newDBSet, newState, active_subgroup_threads, newPc, newCounter)
                            matchedSnapShot == MeaningfulUpdate(newPc, newState, snapShotMap, newDBSet)
                        IN
                            IF matchedSnapShot = {} THEN
                                /\  snapShotMap' = newSnapShotMap
                                /\  state' = newState   
                                /\  DynamicNodeSet' = newDBSet
                                /\  pc' = newPc
                                /\  globalCounter' = newCounter
                            ELSE 
                                LET previousState == CHOOSE db \in matchedSnapShot: TRUE
                                IN
                                    /\ state' = previousState.state
                                    /\ DynamicNodeSet' = previousState.dynamicNodeSet
                                    /\ globalCounter' = previousState.globalCounter
                                    /\ pc' = previousState.pc
                                    /\ UNCHANGED  <<threadLocals, globalVars, snapShotMap>>
                /\  UNCHANGED <<threadLocals, globalVars>>


OpBranchConditional(t, condition, trueLabel, falseLabel) ==
    /\  IsLiteral(trueLabel)
    /\  IsLiteral(falseLabel)
    /\  LET trueLabelVal == GetVal(-1, trueLabel)
            falseLabelVal == GetVal(-1, falseLabel)
            workGroupId == WorkGroupId(t)+1

        IN
            IF EvalExpr(t, WorkGroupId(t)+1, condition) = TRUE THEN
                /\  LET counterNewDBSet == BranchUpdate(workGroupId, t, pc[t], {trueLabelVal, falseLabelVal}, trueLabelVal, {trueLabelVal, falseLabelVal})
                        newCounter == counterNewDBSet[1]
                        newDBSet == counterNewDBSet[2]
                        newState == StateUpdate(workGroupId, t, newDBSet)
                        newPc == [pc EXCEPT ![t] = trueLabelVal]
                        newSnapShotMap == SnapShotUpdate(newDBSet, newState, t, newPc, newCounter)
                        matchedSnapShot == MeaningfulUpdate(newPc, newState, snapShotMap, newDBSet)
                    IN
                        IF matchedSnapShot = {} THEN
                            /\  snapShotMap' = newSnapShotMap
                            /\  state' = newState   
                            /\  DynamicNodeSet' = newDBSet
                            /\  pc' = newPc
                            /\  globalCounter' = newCounter
                        ELSE 
                            LET previousState == CHOOSE db \in matchedSnapShot: TRUE
                            IN
                                /\ state' = previousState.state
                                /\ DynamicNodeSet' = previousState.dynamicNodeSet
                                /\ globalCounter' = previousState.globalCounter
                                /\ pc' = previousState.pc
                                /\ UNCHANGED  <<threadLocals, globalVars, snapShotMap>>
            ELSE
                /\  LET counterNewDBSet == BranchUpdate(workGroupId, t, pc[t], {trueLabelVal, falseLabelVal}, falseLabelVal, {trueLabelVal, falseLabelVal})
                        newCounter == counterNewDBSet[1]
                        newDBSet == counterNewDBSet[2]
                        newState == StateUpdate(workGroupId, t, newDBSet)
                        newPc == [pc EXCEPT ![t] = falseLabelVal]
                        newSnapShotMap == SnapShotUpdate(newDBSet, newState, t, newPc, newCounter)
                        matchedSnapShot == MeaningfulUpdate(newPc, newState, snapShotMap, newDBSet)

                    IN
                        IF matchedSnapShot = {} THEN
                            /\  snapShotMap' = newSnapShotMap
                            /\  state' = newState
                            /\  DynamicNodeSet' = newDBSet
                            /\  pc' = newPc
                            /\  globalCounter' = newCounter
                        ELSE 
                            LET previousState == CHOOSE db \in matchedSnapShot: TRUE
                            IN
                                /\ state' = previousState.state
                                /\ DynamicNodeSet' = previousState.dynamicNodeSet
                                /\ globalCounter' = previousState.globalCounter
                                /\ pc' = previousState.pc
                                /\ UNCHANGED  <<threadLocals, globalVars, snapShotMap>>
    /\  UNCHANGED <<threadLocals, globalVars>>

    

OpSwitchSync(t, selector, default, literals, ids) == 
/\  LET workGroupId == WorkGroupId(t) + 1
        sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
        currentDB == CurrentDynamicNode(workGroupId, t)
        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
    IN
        \* if there are threads in tangle not reaching the instruction point,
        \* or there are threads in unknown set, make current thread waiting
        IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
            /\  state' = [state EXCEPT ![t] = "subgroup"]
            /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
        ELSE 
            /\  LET defaultVal == GetVal(-1, default)
                    literalsVal == [idx \in 1..Len(literals) |-> GetVal(-1, literals[idx])]
                    idsVal == [idx \in 1..Len(ids) |-> GetVal(-1, ids[idx])]
                IN
                    IF EvalExpr(t, WorkGroupId(t)+1, selector) \in SeqToSet(literalsVal) THEN
                        LET val == EvalExpr(t, WorkGroupId(t)+1, selector)
                            index == CHOOSE i \in 1..Len(literalsVal): literalsVal[i] = val 
                        IN
                            LET labelSet == SeqToSet(idsVal) \union {defaultVal}
                                falseLabelSet == (CHOOSE postDom \in PostDominated: postDom.node = idsVal[index]).postDominated \intersect labelSet
                                counterNewDBSet == BranchUpdate(workGroupId, t, pc[t], labelSet, idsVal[index], falseLabelSet)
                                newCounter == counterNewDBSet[1]
                                newDBSet == counterNewDBSet[2]
                                newState == StateUpdate(workGroupId, t, newDBSet)
                                newPc == [pc EXCEPT ![t] = idsVal[index]]
                                newSnapShotMap == SnapShotUpdate(newDBSet, newState, t, newPc, newCounter)
                                matchedSnapShot == MeaningfulUpdate(newPc, newState, snapShotMap, newDBSet)
                            IN
                                IF matchedSnapShot = {} THEN
                                    /\  snapShotMap' = newSnapShotMap
                                    /\  state' = newState
                                    /\  DynamicNodeSet' = newDBSet
                                    /\  pc' = newPc
                                    /\  globalCounter' = newCounter
                                ELSE 
                                    LET previousState == CHOOSE db \in matchedSnapShot: TRUE
                                    IN
                                        /\ state' = previousState.state
                                        /\ DynamicNodeSet' = previousState.dynamicNodeSet
                                        /\ globalCounter' = previousState.globalCounter
                                        /\ pc' = previousState.pc
                                        /\ UNCHANGED  <<threadLocals, globalVars, snapShotMap>>
                    ELSE
                        LET labelSet == SeqToSet(idsVal) \union {defaultVal}
                            falseLabelSet == (CHOOSE postDom \in PostDominated: postDom.node = defaultVal).postDominated \intersect (SeqToSet(idsVal) \union {defaultVal})
                            counterNewDBSet == BranchUpdate(workGroupId, t, pc[t], labelSet, defaultVal, falseLabelSet)
                            newCounter == counterNewDBSet[1]
                            newDBSet == counterNewDBSet[2]
                            newState == StateUpdate(workGroupId, t, newDBSet)
                            newPc == [pc EXCEPT ![t] = defaultVal]
                            newSnapShotMap == SnapShotUpdate(newDBSet, newState, t, newPc, newCounter)
                            matchedSnapShot == MeaningfulUpdate(newPc, newState, snapShotMap, newDBSet)
                        IN
                            IF matchedSnapShot = {} THEN
                                /\  snapShotMap' = newSnapShotMap
                                /\  state' = newState
                                /\  DynamicNodeSet' = newDBSet
                                /\  pc' = newPc
                                /\  globalCounter' = newCounter
                            ELSE 
                                LET previousState == CHOOSE db \in matchedSnapShot: TRUE
                                IN
                                    /\ state' = previousState.state
                                    /\ DynamicNodeSet' = previousState.dynamicNodeSet
                                    /\ globalCounter' = previousState.globalCounter
                                    /\ pc' = previousState.pc
                                    /\ UNCHANGED  <<threadLocals, globalVars, snapShotMap>>
            /\  UNCHANGED <<threadLocals, globalVars>>


OpSwitch(t, selector, default, literals, ids) ==
    /\  LET defaultVal == GetVal(-1, default)
            literalsVal == [idx \in 1..Len(literals) |-> GetVal(-1, literals[idx])]
            idsVal == [idx \in 1..Len(ids) |-> GetVal(-1, ids[idx])]
            workGroupId == WorkGroupId(t)+1
        IN
            IF EvalExpr(t, WorkGroupId(t)+1, selector) \in SeqToSet(literalsVal) THEN
                LET val == EvalExpr(t, WorkGroupId(t)+1, selector)
                    index == CHOOSE i \in 1..Len(literalsVal): literalsVal[i] = val 
                IN
                    /\  LET labelSet == SeqToSet(idsVal) \union {defaultVal}
                            falseLabelSet == (CHOOSE postDom \in PostDominated: postDom.node = idsVal[index]).postDominated \intersect labelSet
                            counterNewDBSet == BranchUpdate(workGroupId, t, pc[t], labelSet, idsVal[index], falseLabelSet)
                            newCounter == counterNewDBSet[1]
                            newDBSet == counterNewDBSet[2]
                            newState == StateUpdate(workGroupId, t, newDBSet)
                            newPc == [pc EXCEPT ![t] = idsVal[index]]
                            newSnapShotMap == SnapShotUpdate(newDBSet, newState, t, newPc, newCounter)
                            matchedSnapShot == MeaningfulUpdate(newPc, newState, snapShotMap, newDBSet)
                        IN
                            IF matchedSnapShot = {} THEN
                                /\  snapShotMap' = newSnapShotMap
                                /\  state' = newState
                                /\  DynamicNodeSet' = newDBSet
                                /\  pc' = newPc
                                /\  globalCounter' = newCounter
                            ELSE 
                                LET previousState == CHOOSE db \in matchedSnapShot: TRUE
                                IN
                                    /\ state' = previousState.state
                                    /\ DynamicNodeSet' = previousState.dynamicNodeSet
                                    /\ globalCounter' = previousState.globalCounter
                                    /\ pc' = previousState.pc
                                    /\ UNCHANGED  <<threadLocals, globalVars, snapShotMap>>
            ELSE
                /\  LET labelSet == SeqToSet(idsVal) \union {defaultVal}
                        falseLabelSet == (CHOOSE postDom \in PostDominated: postDom.node = defaultVal).postDominated \intersect (SeqToSet(idsVal) \union {defaultVal})
                        counterNewDBSet == BranchUpdate(workGroupId, t, pc[t], labelSet, defaultVal, falseLabelSet)
                        newCounter == counterNewDBSet[1]
                        newDBSet == counterNewDBSet[2]
                        newState == StateUpdate(workGroupId, t, newDBSet)
                        newPc == [pc EXCEPT ![t] = defaultVal]
                        newSnapShotMap == SnapShotUpdate(newDBSet, newState, t, newPc, newCounter)
                        matchedSnapShot == MeaningfulUpdate(newPc, newState, snapShotMap, newDBSet)
                    IN
                        IF matchedSnapShot = {} THEN
                            /\  snapShotMap' = newSnapShotMap
                            /\  state' = newState
                            /\  DynamicNodeSet' = newDBSet
                            /\  pc' = newPc
                            /\  globalCounter' = newCounter
                        ELSE 
                            LET previousState == CHOOSE db \in matchedSnapShot: TRUE
                            IN
                                /\ state' = previousState.state
                                /\ DynamicNodeSet' = previousState.dynamicNodeSet
                                /\ globalCounter' = previousState.globalCounter
                                /\ pc' = previousState.pc
                                /\ UNCHANGED  <<threadLocals, globalVars, snapShotMap>>
    /\  UNCHANGED <<threadLocals, globalVars>>

(* structured loop, must immediately precede block termination instruction, which means it must be second-to-last instruction in its block *)
OpLabel(t, label) ==
    /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
    /\  UNCHANGED <<state, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>

(* structured loop, must immediately precede block termination instruction, which means it must be second-to-last instruction in its block *)
OpLoopMerge(t, mergeLabel, continueTarget) ==
    \* because the merge instruction must be the second to last instruction in the block, we can find the currren block by looking at the termination instruction
    /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
    /\  UNCHANGED <<state, threadLocals, globalVars, DynamicNodeSet, globalCounter, snapShotMap>>

OpSelectionMerge(t, mergeLabel) ==
    \* because the merge instruction must be the second to last instruction in the block, we can find the currren block by looking at the termination instruction
    /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
    /\  UNCHANGED <<state, threadLocals, globalVars, DynamicNodeSet, globalCounter, snapShotMap>>

Terminate(t) ==
    LET workGroupId == WorkGroupId(t)+1
    IN
        LET newDBSet == TerminateUpdate(workGroupId, t)
            newState == StateUpdate(workGroupId, t, newDBSet)
        IN 
            /\  DynamicNodeSet' = newDBSet
            /\  state' = [newState EXCEPT ![t] = "terminated"]
            /\  UNCHANGED <<pc, threadLocals, globalVars, globalCounter, snapShotMap>>

OpAssert(t, predicate) ==
    LET workGroupId == WorkGroupId(t)+1
    IN
        IF EvalExpr(t, workGroupId, predicate) = FALSE THEN
            /\  Print("Assert failed", FALSE)
        ELSE
            /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
            /\  UNCHANGED <<state, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>

ExecuteInstruction(t) ==
    LET workGroupId == WorkGroupId(t)+1
        currentInstr == ThreadInstructions[t][pc[t]]
    IN
        IF state[t] # "terminated" THEN
            IF  currentInstr = "Terminate" THEN
                Terminate(t)
            ELSE IF currentInstr = "Assignment" THEN
                /\  Assignment(t, {Mangle(t,ThreadArguments[t][pc[t]][1])})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state,  DynamicNodeSet, globalCounter, snapShotMap>>
            ELSE IF currentInstr = "GetGlobalId" THEN
                GetGlobalId(t, ThreadArguments[t][pc[t]][1])
            ELSE IF currentInstr = "OpAtomicIncrement" THEN
                OpAtomicIncrement(t, ThreadArguments[t][pc[t]][1])
            ELSE IF currentInstr = "OpAtomicDecrement" THEN
                OpAtomicDecrement(t, ThreadArguments[t][pc[t]][1])
            ELSE IF currentInstr = "OpLogicalOr" THEN 
                OpLogicalOr(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpLogicalAnd" THEN
                OpLogicalAnd(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpLogicalEqual" THEN
                OpLogicalEqual(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpLogicalNotEqual" THEN
                OpLogicalNotEqual(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpLogicalNot" THEN
                OpLogicalNot(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
            ELSE IF currentInstr = "OpBitcast" THEN
                OpBitcast(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
            ELSE IF currentInstr = "OpShiftLeftLogical" THEN
                OpShiftLeftLogical(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpShiftRightLogical" THEN
                OpShiftRightLogical(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpEqual" THEN
                OpEqual(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpNotEqual" THEN
                OpNotEqual(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpLess" THEN
                OpLess(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpLessOrEqual" THEN
                OpLessOrEqual(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpGreater" THEN
                OpGreater(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpGreaterOrEqual" THEN
                OpGreaterOrEqual(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpBitwiseOr" THEN
                OpBitwiseOr(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpBitwiseAnd" THEN
                OpBitwiseAnd(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpAdd" THEN
                OpAdd(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpAtomicAdd" THEN
                OpAtomicAdd(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpSub" THEN
                OpSub(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpAtomicSub" THEN
                OpAtomicSub(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpAtomicOr" THEN
                IF IsCollectiveInstruction(currentInstr) \/ IsSynchronousInstruction(currentInstr) THEN
                    OpAtomicOrSync(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
                ELSE
                    OpAtomicOr(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpAtomicAnd" THEN
                OpAtomicAnd(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpMul" THEN
                OpMul(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpMod" THEN
                OpMod(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpAtomicExchange" THEN
                OpAtomicExchange(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpAtomicCompareExchange" THEN
                OpAtomicCompareExchange(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3], ThreadArguments[t][pc[t]][4])
            ELSE IF currentInstr = "OpAtomicLoad" THEN
                IF IsCollectiveInstruction(currentInstr) THEN 
                    OpAtomicLoadCollective(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
                ELSE IF IsSynchronousInstruction(currentInstr) THEN 
                    OpAtomicLoadSync(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
                ELSE
                    OpAtomicLoad(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
            ELSE IF currentInstr = "OpAtomicStore" THEN
                IF IsCollectiveInstruction(currentInstr) THEN
                    OpAtomicStoreCollective(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
                ELSE IF IsSynchronousInstruction(currentInstr) THEN 
                    OpAtomicStoreSync(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
                ELSE
                    OpAtomicStore(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
            ELSE IF currentInstr = "OpBranch" THEN
                IF IsCollectiveInstruction(currentInstr) THEN 
                    OpBranchSync(t, ThreadArguments[t][pc[t]][1])
                ELSE
                    OpBranch(t, ThreadArguments[t][pc[t]][1])
            ELSE IF currentInstr = "OpBranchConditional" THEN
                IF IsCollectiveInstruction(currentInstr) THEN 
                    OpBranchConditionalSync(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
                ELSE
                    OpBranchConditional(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpSwitch" THEN
                IF IsCollectiveInstruction(currentInstr) THEN 
                    OpSwitchSync(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3], ThreadArguments[t][pc[t]][4])
                ELSE
                    OpSwitch(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3], ThreadArguments[t][pc[t]][4])
            ELSE IF currentInstr = "OpControlBarrier" THEN
                OpControlBarrier(t, ThreadArguments[t][pc[t]][1])
            ELSE IF currentInstr = "OpGroupAll" THEN
                OpGroupAll(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpGroupAny" THEN
                OpGroupAny(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpGroupNonUniformAll" THEN
                OpGroupNonUniformAll(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpGroupNonUniformAllEqual" THEN
                OpGroupNonUniformAllEqual(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpGroupNonUniformAny" THEN
                OpGroupNonUniformAny(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpGroupNonUniformBroadcast" THEN
                OpGroupNonUniformBroadcast(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3], ThreadArguments[t][pc[t]][4])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpLoopMerge" THEN
                OpLoopMerge(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpSelectionMerge" THEN
                OpSelectionMerge(t, ThreadArguments[t][pc[t]][1])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpLabel" THEN
                OpLabel(t, ThreadArguments[t][pc[t]][1])
            ELSE IF ThreadInstructions[t][pc[t]] = "Assert" THEN
                OpAssert(t, ThreadArguments[t][pc[t]][1])
            ELSE
                FALSE
        ELSE 
            /\ UNCHANGED << threadVars, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>


(* This property ensures all the instructions in all threads are bounded to the instruction set *)
AllInstructionsWithinSet ==
    \A t \in Threads:
        \A ins \in DOMAIN ThreadInstructions[t]:
            ThreadInstructions[t][ins] \in InstructionSet

AllThreadStatesAreBounded ==
    \A t \in Threads:
        state[t] \in ThreadState

(* This property ensures that the program counter of all threads are bounded *)

====
