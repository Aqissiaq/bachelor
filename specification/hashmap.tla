------------------------------ MODULE hashmap ------------------------------
(*****************************************************************************)
(*This module describes a hashmap to be used for testing with Shalev et al.'s*)
(*split-ordered list implementation of the data structure                    *)
(*****************************************************************************)

EXTENDS Integers

CONSTANTS NULL, PossibleKeys, PossibleValues

VARIABLES keys, map


(*******************************************************)
(*Initial state has empty map and no keys              *)
(*******************************************************)

HashmapInit ==  /\ keys = {}
                /\ map = [k \in PossibleKeys |-> NULL]

(*******************************************************)
(*Insert changes exactly one mapping of the hashmap    *)
(*and adds one key to the set of keys                  *)
(*******************************************************)
Insert ==   \exists k \in PossibleKeys :
                \exists v \in PossibleValues :
                    /\ keys' = keys \union {k}
                    /\ map' = [map EXCEPT ![k] = v]

(*******************************************************)
(*Remove sets exactly one mapping to NULL              *)
(*******************************************************)
Remove ==   \exists k \in PossibleKeys :
                /\ keys' = keys \ {k}
                /\ map' = [map EXCEPT ![k] = NULL]

(*******************************************************)
(*Next is either an insert or a remove                 *)
(*******************************************************)          
HashmapNext ==  \/ Insert
                \/ Remove

(*******************************************************)
(*TypeOK asserts all keys and values are of the right type*)
(*******************************************************) 
TypeOK ==   \forall k \in keys :
                /\ k \in PossibleKeys
                /\ map[k] \in PossibleValues

(*******************************************************)
(*KeyHasValue asserts that every key is mapped to a value*)
(*******************************************************) 
KeyHasValue == \forall k \in keys : ~(map[k] = NULL)

(*******************************************************)
(*The hashmap specification as a temporal formula      *)
(*******************************************************) 
HashmapSpec == HashmapInit /\ [][HashmapNext]_<<keys, map>>
=============================================================================