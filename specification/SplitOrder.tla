--------------------------------- MODULE SplitOrder ---------------------------------
(*************************************************************************************)
(*This module implements a hashmap using Shalev et al.'s split-ordered list structure*)
(*************************************************************************************)

EXTENDS Integers

CONSTANTS NULL, PossibleKeys, PossibleValues, LoadFactor, MaxSize

VARIABLES keys, list, buckets, size, count

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
            /\ list = [n \in 0..255 |-> IF n = 0 THEN SODummyKey(0) ELSE NULL]
            /\ buckets = [m \in PossibleKeys |-> IF m = 0 THEN SODummyKey(0) ELSE NULL]
            /\ size = 1
            /\ count = 0

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

(********************************************************)
(*Find the value of the key k in the bucket b           *)
(*Results in the value if b is initialized and k is in b*)
(********************************************************)
ListFind(b, k) == IF k > b /\ list[b] /= NULL THEN list[k] ELSE NULL

(*SOFind finds a key in the map*)
SOFind(k) == IF buckets[k % size] = NULL
                THEN NULL \* should initialize bucket, but also needs a "return value"
                ELSE ListFind(buckets[k % size], k)

Min(a, b) == IF a > b THEN b ELSE a
BucketGrow == IF count /= 0 /\ size \div count > LoadFactor
                THEN size' = Min(size * 2, MaxSize) /\ UNCHANGED <<keys, list, buckets, count>> 
                ELSE UNCHANGED <<keys, list, buckets, count, size>>

(****************************)
(*Inserting into the buckets*)
(****************************)
BucketInsert(k, v) == (*Either a bucket needs to be initialized*)
                    \/  /\ buckets[k % size] = NULL
                        /\ BucketInit(k % size)
                        /\ ListInsert(SORegularKey(k), v)
                        /\ keys' = keys \union {k}                      
                      (*Or the bucket is already initialized*)
                    \/  /\ buckets[k % size] /= NULL
                        /\ ListInsert(SORegularKey(k), v)
                        /\ keys' = keys \union {k}
                        /\ UNCHANGED <<buckets>>

(***************************)
(*Removing from the buckets*)
(***************************)                
BucketRemove(k) == /\ ListRemove(SORegularKey(k))
                   /\ keys' = keys \ {k}
                   /\ UNCHANGED <<buckets>>


SOInsert == /\  \E k \in PossibleKeys :
                    \E v \in PossibleValues :
                        BucketInsert(k, v)
            /\ UNCHANGED size

SORemove == /\  \E k \in PossibleKeys :
                    BucketRemove(k)
            /\ UNCHANGED size


(**************************)
(*The Next for split order*)
(**************************)
SONext ==   \/ SOInsert
            \/ SORemove
            \/ BucketGrow

(**************************)
(*Split-order spec        *)
(**************************)
SOSpec == SOInit /\ [][SONext]_<<keys, list, buckets, size, count>>

(*********)
(*A refinement mapping of the hashmap spec with the map defined by the SOFind action*)
(***********)
INSTANCE hashmap WITH map <- [k \in PossibleKeys |-> SOFind(k)]
(********************************)
(*Split-order implements hashmap*)
(********************************)
THEOREM SOSpec => HashmapSpec

======================================================================================