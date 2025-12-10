Require Extraction.
Require Import String.
From RFXP Require Import Features DT RF CNF Sat.

Module Type InputDataSig.

    Definition class := string.

    Parameter n_features : nat.

    Parameter features : featureSig n_features.

    Parameter random_forest : randomForest features.

    Parameter instance : featureVec features.

End InputDataSig.


Module Type MainSig (D : InputDataSig).

    Parameter main : unit -> D.class.

End MainSig.


Module Main (Import D : InputDataSig) : MainSig D.

    Definition main (_ : unit) : class :=
        evalRF features random_forest instance.

End Main.
