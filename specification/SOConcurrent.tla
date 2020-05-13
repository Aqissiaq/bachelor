    ---------------------------- MODULE SOConcurrent ----------------------------

EXTENDS Integers, Sequences, Bags

CONSTANTS NULL, PossibleKeys, PossibleValues, LoadFactor, MaxSize, MaxActiveOps

VARIABLES list, buckets, size, count, activeOps

ASSUME
    /\ PossibleKeys \subseteq 0..15
    /\ NULL \notin PossibleKeys
    /\ NULL \notin PossibleValues

OperationStates ==
    (*Set of all possible active operations            *)
    (*They can be of type insert, delete or bucket_init*)
    (*Step denotes the current step of the operation   *)
    [type: {"insert"}, step : 1..4, key : PossibleKeys, value : PossibleValues]
        \union 
    [type: {"delete"}, step : 1..3, key : PossibleKeys]
        \union 
    [type: {"bucket_init"}, step : 1..3, bucket : 0..(MaxSize-1)]

(*Lookup table for bit-reversed keys with MSB set*)
SORegularKey(k) ==  CASE k = 0 -> 1
                     [] k = 1 -> 9
                     [] k = 2 -> 5
                     [] k = 3 -> 13
                     [] k = 4 -> 3
                     [] k = 5 -> 11
                     [] k = 6 -> 7
                     [] k = 7 -> 15
                     [] k = 8 -> 1
                     [] k = 9 -> 9
                     [] k = 10 -> 5
                     [] k = 11 -> 13
                     [] k = 12 -> 3
                     [] k = 13 -> 11
                     [] k = 14 -> 7
                     [] k = 15 -> 15

(*Lookup table for bit-reversed keys*)
SODummyKey(k) ==    CASE k = 0 -> 0
                     [] k = 1 -> 8
                     [] k = 2 -> 4
                     [] k = 3 -> 12
                     [] k = 4 -> 2
                     [] k = 5 -> 10
                     [] k = 6 -> 6
                     [] k = 7 -> 14
                     [] k = 8 -> 1
                     [] k = 9 -> 9
                     [] k = 10 -> 5
                     [] k = 11 -> 13
                     [] k = 12 -> 3
                     [] k = 13 -> 11
                     [] k = 14 -> 7
                     [] k = 15 -> 15

(*Lookup table for parent buckets*)
Parent(b) ==    CASE b = 0 -> 0
                     [] b = 1 -> 0
                     [] b = 2 -> 0
                     [] b = 3 -> 1
                     [] b = 4 -> 0
                     [] b = 5 -> 1
                     [] b = 6 -> 2
                     [] b = 7 -> 3
                     [] b = 8 -> 0
                     [] b = 9 -> 1
                     [] b = 10 -> 2
                     [] b = 11 -> 3
                     [] b = 12 -> 8
                     [] b = 13 -> 5
                     [] b = 14 -> 6
                     [] b = 15 -> 7


SOInit ==   /\ activeOps = EmptyBag
            /\ list = [n \in 0..16 |-> IF n = 0 THEN SODummyKey(0) ELSE NULL]
            /\ buckets = [m \in 0..(MaxSize-1) |-> IF m = 0 THEN SODummyKey(0) ELSE NULL]
            /\ size = 1
            /\ count = 0
            
(*Begin an insert operation*)
Insert(k, v) == activeOps' = activeOps (+) SetToBag({[type|-> "insert", step |-> 1, key |-> k, value |-> v]})
(*Begin a delete operation*)
Delete(k) == activeOps' = activeOps (+) SetToBag({[type|-> "delete", step |-> 1, key |-> k]})
(*Begin a bucket_init operation*)
BucketInit(b) == activeOps' = activeOps (+) SetToBag({[type|-> "bucket_init", step |-> 1, bucket |-> b]})

NextStep(op) == activeOps' = (activeOps (-) SetToBag({op})) (+) SetToBag({[op EXCEPT !["step"] = op.step + 1]})
End(op) == activeOps' = activeOps (-) SetToBag({op})
Min(a, b) == IF a > b THEN b ELSE a

(*Steps of an insert operation*)
Insert1 == 
    (*Start a bucket_init if necessary*)
    \E op \in BagToSet(activeOps) :
        /\ op.type = "insert"
        /\ op.step = 1
        /\ IF buckets[op.key % size] = NULL
            (*Kind of ugly because nextstep and "begin bucket_init" both modify the state of activeOps and need to be combined*)
            THEN activeOps' = (activeOps (-) SetToBag({op}))
                                    (+) SetToBag({[op EXCEPT !["step"] = op.step + 1]})
                                    (+) SetToBag({[type |-> "bucket_init", step |-> 1, bucket |-> op.key % size]})
            ELSE NextStep(op)
        /\ UNCHANGED <<list, buckets, size, count>>

Insert2 ==
    (*If key is already in list, end operation. Else insert in list*)
    \E  op \in BagToSet(activeOps) :
        /\ op.type = "insert"
        /\ op.step = 2
        /\  IF list[SORegularKey(op.key)] = NULL
                THEN list' = [list EXCEPT ![SORegularKey(op.key)] = op.value] /\ NextStep(op) 
                ELSE End(op) /\ UNCHANGED list
        /\ UNCHANGED <<buckets, size, count>>

Insert3 ==
    (*Increment count*)
    \E  op \in BagToSet(activeOps) :
        /\ op.type = "insert"
        /\ op.step = 3
        /\ count' = count +1
        /\ NextStep(op)
        /\ UNCHANGED <<list, buckets, size>>

Insert4 ==
    (*Change size if loadfactor is exceeded and end insert*)
    \E  op \in BagToSet(activeOps) :
    /\ op.type = "insert"
    /\ op.step = 4
    /\ IF count \div size > LoadFactor THEN size' = Min(2 * size, MaxSize) ELSE UNCHANGED size
    /\ End(op)
    /\ UNCHANGED <<list, buckets, count>>

(*Steps of a delete operation*)
Delete1 ==
    (*Start a bucket_init if necessary*)
    \E  op \in BagToSet(activeOps) :
        /\ op.type = "delete"
        /\ op.step = 1
        /\ IF buckets[op.key % size] = NULL
                THEN activeOps' = (activeOps (-) SetToBag({op}))
                                        (+) SetToBag({[op EXCEPT !["step"] = op.step + 1]})
                                        (+) SetToBag({[type|-> "bucket_init", step |-> 1, bucket |-> op.key % size]})
                ELSE NextStep(op)
        /\ UNCHANGED <<list, buckets, size, count>>

Delete2 ==
    (*If the key is not there, end operation. Else, remove it*)
    \E  op \in BagToSet(activeOps) :
        /\ op.type = "delete"
        /\ op.step = 2
        /\  IF list[SORegularKey(op.key)] = NULL
                THEN /\ End(op)
                     /\ UNCHANGED list
                ELSE /\ list' = [list EXCEPT ![SORegularKey(op.key)] = NULL]
                     /\ NextStep(op)
        /\ UNCHANGED <<buckets, size, count>>        

Delete3 ==
    (*Decrement count*)
    \E  op \in BagToSet(activeOps) :
        /\ op.type = "delete"
        /\ op.step = 3
        /\ count' = count - 1
        /\ End(op)
        /\ UNCHANGED <<buckets, list, size>>

(*Steps of a bucket init*)
BucketInit1 ==
    (*Start a bucket_init on parent bucket if needed*)
    \E  op \in BagToSet(activeOps) :
        /\ op.type = "bucket_init"
        /\ op.step = 1
        /\ IF buckets[Parent(op.bucket)] = NULL
                THEN BucketInit(Parent(op.bucket))
                ELSE TRUE
        /\ NextStep(op)
        /\ UNCHANGED <<buckets, size, count, list>>

BucketInit2 ==
    (*If there is no dummy node in the list, insert it*)
    \E  op \in BagToSet(activeOps) :
        /\ op.type = "bucket_init"
        /\ op.step = 2
        /\  IF list[SODummyKey(op.bucket)] = NULL
                THEN list' = [list EXCEPT ![SODummyKey(op.bucket)] = op.bucket]
                ELSE UNCHANGED list
        /\ NextStep(op)
        /\ UNCHANGED <<buckets, size, count>>

BucketInit3 ==
    (*Point bucket to dummy node*)
    \E  op \in BagToSet(activeOps) :
        /\ op.type = "bucket_init"
        /\ op.step = 3
        /\ buckets' = [buckets EXCEPT ![op.bucket] = SODummyKey(op.bucket)]
        /\ End(op)
        /\ UNCHANGED <<list, size, count>>

SONext ==
    \/  /\ \E k \in PossibleKeys :
             \E v \in PossibleValues :
                Insert(k, v)
        /\ BagCardinality(activeOps) < MaxActiveOps
        /\ UNCHANGED <<buckets, count, list, size>>
    \/  /\ \E k \in PossibleKeys :
            Delete(k)
        /\ BagCardinality(activeOps) < MaxActiveOps
        /\ UNCHANGED <<buckets, count, list, size>>
    \/ Insert1
    \/ Insert2
    \/ Insert3
    \/ Insert4
    \/ Delete1
    \/ Delete2
    \/ Delete3
    \/ BucketInit1
    \/ BucketInit2
    \/ BucketInit3


BucketsInitialized ==
    \A i \in 0..(size-1) :
        \/ buckets[i] = NULL
        \/ buckets[i] = SODummyKey(i) /\ list[SODummyKey(i)] = i

OperationsOK ==
    \A  op \in BagToSet(activeOps) :
        op \in OperationStates
        
(*An insert with key not in map will succeed*)
InsertSucceeds ==
    \A op \in OperationStates :
        IF op.type = "insert"
        (*This test is needed to avoid checking fields that do not exist in other types of operations*)
        THEN
            /\ op \in BagToSet(activeOps)
            /\ op.step = 1
            /\ list[SORegularKey(op.key)] = NULL
         => <>(list[SORegularKey(op.key)] = op.value)
        ELSE TRUE
        
(*An insert with key in map will not reach step 3*)
InsertFails ==
    \A op \in OperationStates :
        IF op.type = "insert"
        THEN
            /\ op \in BagToSet(activeOps)
            /\ op.step = 1
            /\ list[SORegularKey(op.key)] /= NULL
         => []<>(~([op EXCEPT !["step"] = 3] \in BagToSet(activeOps)))
        ELSE TRUE
        
(*A delete with key in map will succeed*)
DeleteSucceeds ==
    \A op \in OperationStates :
        IF op.type = "delete"
        THEN
            /\ op \in BagToSet(activeOps)
            /\ op.step = 1
            /\ list[SORegularKey(op.key)] /= NULL
        => <>(list[SORegularKey(op.key)] = NULL)
        ELSE TRUE
        
(*A delete with key not in map will not reach step 3*)
DeleteFails ==
    \A op \in OperationStates :
            IF op.type = "delete"
            THEN
                /\ op \in BagToSet(activeOps)
                /\ op.step = 1
                /\ list[SORegularKey(op.key)] = NULL
            => []<>(~([op EXCEPT !["step"] = 3] \in BagToSet(activeOps)))
            ELSE TRUE
                

=============================================================================
\* Modification History
\* Last modified Wed May 13 13:30:47 CEST 2020 by aqissiaq
\* Created Sat Apr 18 15:31:35 CEST 2020 by aqissiaq
