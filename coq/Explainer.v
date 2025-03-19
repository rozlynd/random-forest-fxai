Require Extraction.
From RFXP Require Import Features DT RF CNF Sat.

Module Type InputDataSig.

    Parameter class : Set.

    Parameter n_features : nat.

    Parameter features : featureList n_features.

    Parameter decision_tree : decisionTree class features.

    Parameter instance : featureSpace features.

End InputDataSig.


Module Type MainSig (D : InputDataSig).

    Parameter main : unit -> D.class.

End MainSig.


Module Main (Import D : InputDataSig) : MainSig D.

    Definition main (_ : unit) : class :=
        evalDT class features decision_tree instance.

End Main.
