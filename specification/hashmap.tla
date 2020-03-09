------------------------------ MODULE hashmap ------------------------------
(*****************************************************************************)
(*This module describes a hashmap to be used for testing with Shalev et al.'s*)
(*split-ordered list implementation of the data structure                    *)
(*****************************************************************************)

EXTENDS Integers, Bags

CONSTANTS NULL, PossibleKeys, PossibleValues

VARIABLES keys, Hashmap


(*******************************************************)
(*Initial state has empty map and all possible values  *)
(*******************************************************)

Init ==     /\ keys = EmptyBag
            /\ Hashmap = [k \in PossibleKeys |-> NULL]

(*******************************************************)
(*Insert changes exactly one mapping of the hashmap    *)
(*******************************************************)
Insert ==   \exists k \in PossibleKeys :
                \exists v \in PossibleValues :
                    /\ keys' = IF BagIn(k, keys) THEN keys ELSE keys (+) SetToBag({k})
                    /\ Hashmap' = [Hashmap EXCEPT ![k] = v]

(*******************************************************)
(*Remove sets exactly one mapping to the emtpy set     *)
(*******************************************************)
Remove ==   \exists k \in BagToSet(keys) :
                /\ keys' = keys (-) SetToBag({k})
                /\ Hashmap' = [Hashmap EXCEPT ![k] = NULL]

(*******************************************************)
(*Next is either an insert or a remove                 *)
(*******************************************************)          
Next ==     \/ Insert
            \/ Remove

(*******************************************************)
(*TypeOK asserts all keys are of the right type         *)
(*******************************************************) 
TypeOK ==   \forall k \in BagToSet(keys) :
                /\ k \in PossibleKeys
                /\ Hashmap[k] \in PossibleValues

(*******************************************************)
(*KeyUnique asserts there are no duplicate keys        *)
(*******************************************************) 
KeyUnique == \forall k \in BagToSet(keys) : CopiesIn(k, keys) = 1

(*******************************************************)
(*KeyHasValue asserts that every key is mapped to a value*)
(*******************************************************) 
KeyHasValue == \forall k \in BagToSet(keys) : ~(Hashmap[k] = NULL)
=============================================================================
\* Modification History
\* Last modified Sat Mar 07 16:11:23 CET 2020 by aqissiaq
\* Created Sat Mar 07 15:14:36 CET 2020 by aqissiaq
