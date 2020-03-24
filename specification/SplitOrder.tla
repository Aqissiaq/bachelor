--------------------------------- MODULE SplitOrder ---------------------------------
(*************************************************************************************)
(*This module implements a hashmap using Shalev et al.'s split-ordered list structure*)
(*************************************************************************************)

EXTENDS Integers

CONSTANTS NULL, PossibleKeys, PossibleValues

VARIABLES map, keys
(**************************)
(*The Init for split-order*)
(**************************)
SOInit ==   /\ keys = {}
            /\ map = [k \in PossibleKeys |-> NULL]

(**************************)
(*The Next for split order*)
(**************************)
SONext ==   /\ keys' = keys \union {"k2"}
            /\ map' = [map EXCEPT !["k2"] = 1]

(**************************)
(*Split-order spec        *)
(**************************)
SOSpec == SOInit /\ [][SONext]_<<map, keys>>

INSTANCE  hashmap
(********************************)
(*Split-order implements hashmap*)
(********************************)
THEOREM SOSpec => HashmapSpec

======================================================================================