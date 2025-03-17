Require Import List.
Import ListNotations.

From RFXP Require Import Features DT.


Section RandomForests.

    Context (class : Set) {n : nat} (fs : featureList n).

    Definition randomForest := list (decisionTree class fs).

    (* TODO *)

End RandomForests.
