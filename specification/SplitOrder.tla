--------------------------------- MODULE SplitOrder ---------------------------------
(*************************************************************************************)
(*This module implements a hashmap using Shalev et al.'s split-ordered list structure*)
(*************************************************************************************)

EXTENDS Integers

CONSTANTS NULL, PossibleKeys, PossibleValues, LoadFactor, MaxSize

VARIABLES keys, AuxKeys, list, buckets, size, count, map

ASSUME
    /\ PossibleKeys \subseteq 0..15
    /\ NULL \notin PossibleKeys
    /\ NULL \notin PossibleValues


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

(****************************************************)
(*The Init for split-order                          *)
(*keys is initially empty                           *)
(*the map maps every possible key to NULL           *)
(*The list initially contains only the 0 dummy node *)
(****************************************************)
SOInit ==   /\ keys = {}
            /\ AuxKeys = {}
            /\ list = [n \in 0..255 |-> IF n = 0 THEN SODummyKey(0) ELSE NULL]
            /\ buckets = [m \in PossibleKeys |-> IF m = 0 THEN SODummyKey(0) ELSE NULL]
            /\ size = 1
            /\ count = 0
            /\ map = [k \in PossibleKeys |-> NULL]

(**********************************)
(*Inserting into the "linked list"*)
(**********************************)
ListInsert(k, v) == IF list[k] = NULL
                        THEN list' = [list EXCEPT ![k] = v] /\ count' = count + 1
                        ELSE UNCHANGED <<list, count>>

(*********************************)
(*Removing from the "linked list"*)
(*********************************)
ListRemove(k) == IF list[k] = NULL
                    THEN UNCHANGED <<list, count>>
                    ELSE list' = [list EXCEPT ![k] = NULL] /\ count' = count - 1

(*********************************)
(*Recursively initializes buckets*)
(*********************************)
RECURSIVE BucketInit(_)
BucketInit(b) == IF buckets[Parent(b)] = NULL /\ Parent(b) /= 0
                    THEN BucketInit(Parent(b))
                    ELSE buckets' = [buckets EXCEPT ![b] = SODummyKey(b)]

(**********************************************)
(*Find the value of the key k in the bucket b *)
(*Results in the value if k is in b           *)
(**********************************************)
ListFind(b, k) == IF k > b THEN list[k] ELSE NULL

(*****************************************************)
(*SOFind updates the state of the map and keys       *)
(*variables by searching through the buckets and list*)
(*****************************************************)
SOFind == \E k \in AuxKeys :
                /\ keys' = keys \union {k}
                /\ AuxKeys' = AuxKeys \ {k}
                /\ IF buckets[k % size] = NULL
                     THEN /\ BucketInit(k % size)
                          /\ map' = [map EXCEPT ![k] = ListFind(k % size, SORegularKey(k))]
                     ELSE /\ UNCHANGED buckets
                          /\ map' = [map EXCEPT ![k] = ListFind(k % size, SORegularKey(k))]

Min(a, b) == IF a > b THEN b ELSE a
BucketGrow == IF count \div size > LoadFactor
                THEN size' = Min(size * 2, MaxSize) 
                ELSE UNCHANGED size

(****************************) 
(*Inserting into the buckets*)
(****************************)
BucketInsert(k, v) == (*Either a bucket needs to be initialized*)
                    \/  /\ buckets[k % size] = NULL
                        /\ BucketInit(k % size)
                        /\ ListInsert(SORegularKey(k), v)
                        /\ AuxKeys' = AuxKeys \union {k}                      
                      (*Or the bucket is already initialized*)
                    \/  /\ buckets[k % size] /= NULL
                        /\ ListInsert(SORegularKey(k), v)
                        /\ AuxKeys' = AuxKeys \union {k}
                        /\ UNCHANGED <<buckets>>

(***************************)
(*Removing from the buckets*)
(***************************)                
BucketRemove(k) == /\ ListRemove(SORegularKey(k))
                   /\ AuxKeys' = AuxKeys \ {k}
                   /\ UNCHANGED <<buckets>>

SOInsert == /\  \E k \in PossibleKeys :
                    \E v \in PossibleValues :
                        BucketInsert(k, v)

SORemove == /\  \E k \in PossibleKeys :
                    BucketRemove(k)

(**************************)
(*The Next for split order*)
(**************************)
SONext ==   \/ SOInsert /\ BucketGrow /\ UNCHANGED <<map, keys>>
            \/ SORemove /\ UNCHANGED <<size, map, keys>>
            \/ SOFind   /\ UNCHANGED <<size, count, list>>
            

(**************************)
(*Split-order spec        *)
(**************************)
SOSpec == SOInit /\ [][SONext]_<<keys, AuxKeys, list, buckets, size, count, map>>

(*******************************************************************)
(*An instance of the hashmap spec is needed to prove implementation*)
(*******************************************************************)
INSTANCE hashmap

(********************************)
(*Split-order implements hashmap*)
(********************************)
THEOREM SOSpec => HashmapSpec

(*************************************)
(*Type correctness of keys and values*)
(*************************************)
SOTypeOK == \forall k \in AuxKeys :
                /\ k \in PossibleKeys
                /\ list[SORegularKey(k)] \in PossibleValues

(***************************************************************)
(*Each bucket is either uninitialized or points to a dummy node*)
(***************************************************************)
SOBucketOK == \forall n \in 0..size-1 :
                    \/ buckets[n] = NULL
                    \/ buckets[n] = SODummyKey(n)
======================================================================================