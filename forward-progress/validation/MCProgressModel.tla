---- MODULE MCProgressModel ----
EXTENDS Integers, Naturals, Sequences, MCThreads, TLC, FiniteSets

VARIABLES fairExecutionSet, selected, runningThread

vars == <<fairExecutionSet, pc, state, selected, runningThread, threadLocals, globalVars, DynamicNodeSet, snapShotMap, globalCounter>>

UniverseOfAllWGs == {0, 1}

InitState ==
    /\ selected = -1
    /\ runningThread = -1

InitOBE ==
    /\  fairExecutionSet = {} 

InitHSA ==
    /\  fairExecutionSet = {0}

InitScheduler ==
    /\  IF Scheduler = "OBE" THEN
            /\  InitOBE
        ELSE IF Scheduler = "HSA" THEN 
            /\  InitHSA
        ELSE
            /\  FALSE
    
Init ==
    /\  InitProgram
    /\  InitThreads
    /\  InitScheduler
    /\  InitState
    /\  InitSnapShotMap
    \* /\  converge = FALSE

OBEUpdateFairExecutionSet(t) ==
    \* get the workgroup id of thread t, and update fair execution set based on the workgroup id of t
    LET workgroupId == WorkGroupId(t) IN 
        \* if thread t's workgroup is not in fairExecutionSet and there exist one thread in the workgroup that is not terminated, add the workgroup to fairExecutionSet
        IF workgroupId \notin fairExecutionSet /\ \E st \in ThreadsWithinWorkGroup(workgroupId): pc[st] < Len(ThreadInstructions[st]) THEN
            /\  fairExecutionSet' = fairExecutionSet \union {workgroupId}
        \* if thread t's workgroup is in fairExecutionSet and all threads in the workgroup are terminated, remove the workgroup from fairExecutionSet
        ELSE IF workgroupId \in fairExecutionSet /\ \A st \in ThreadsWithinWorkGroup(workgroupId): state[st] = "terminated" THEN
            /\  fairExecutionSet' = fairExecutionSet \ {workgroupId}
        ELSE
            /\  UNCHANGED fairExecutionSet


HSAUpdateFairExecutionSet(t) ==
    \* get the workgroup id that has lowest id and contains non-terminated thread
    LET threadsNotTerminated == {tid \in Threads : state[tid] # "terminated"} IN
            IF threadsNotTerminated # {} THEN 
                /\  fairExecutionSet' = {WorkGroupId(Min(threadsNotTerminated))}
            ELSE 
                /\  fairExecutionSet' = {}
    
UpdateFairExecutionSet(t) == 
    /\  IF Scheduler = "OBE" THEN
        /\  OBEUpdateFairExecutionSet(t)
        ELSE IF Scheduler = "HSA" THEN 
        /\  HSAUpdateFairExecutionSet(t)
        ELSE
        /\  Print("Uknown Scheduler", FALSE)

GetMaxIterDifference(nodeSet) ==
    LET SetMax(S) == CHOOSE s \in S : \A t \in S : s.iter >= t.iter
        SetMin(S) == CHOOSE s \in S : \A t \in S : s.iter <= t.iter
    IN
        SetMax(nodeSet).iter - SetMin(nodeSet).iter
        
IterationNotExceedsBound ==
    \A DB \in DynamicNodeSet:
        LET iterationStack == DB.iterationVec IN
            \A i \in 1..Len(iterationStack): iterationStack[i].iter <= 4

\* PickAnyWorkGroupInFairExecutionSet ==
\*            <>[] (\A wg \in fairExecutionSet:  selected = wg)

PickAnyWorkGroupInFairExecutionSet ==
    \A wg \in UniverseOfAllWGs :
        [] ( wg \in fairExecutionSet => <> (selected = wg) )

Execute(t) == 
        /\  ExecuteInstruction(t)
        /\  UpdateFairExecutionSet(t)
        /\  selected' = WorkGroupId(t)
        /\  runningThread' = t

Step ==
    LET ThreadsReady == {t \in Threads: state[t] = "ready"}
        IN
            \*if there is any thread that is not terminated, execute it
            IF ThreadsReady # {} THEN
                IF runningThread = -1 \/ IsMemoryOperation(ThreadInstructions[runningThread][pc[runningThread]]) \/ runningThread \notin ThreadsReady THEN
                    \E t \in ThreadsReady:
                        /\  Execute(t)
                ELSE
                    /\  Execute(runningThread)
                    \* \E t \in ThreadsReady:
                    \*     /\  Execute(t)
        
            ELSE
                /\ UNCHANGED vars
                /\ UNCHANGED snapShotMap
                /\ UNCHANGED globalCounter
\* Deadlock means reaching a state in which Next is not enabled.
Next ==
    Step

ViewFunction == <<pc, state, threadLocals, globalVars, DynamicNodeSet, selected, runningThread>>

(* Fairness properties *)

Fairness ==
    /\  <>[](ENABLED <<Step>>_vars) => ([]<><<Step>>_vars /\ PickAnyWorkGroupInFairExecutionSet)
    
(* Specification *)
Spec == 
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

\* eventually all threads are always terminated
EventuallyAlwaysTerminated ==
    \A t \in Threads: <>[](state[t] = "terminated")

CounterConstraint == globalCounter <= 100

    
Liveness == 
    /\  EventuallyAlwaysTerminated

====