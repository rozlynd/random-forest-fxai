Require Extraction.
From RFXP Require Import Features DT.

Parameter class : Set.
Extract Constant class => "string".

Record input_data := {
    n_features : nat ;
    features : featureList n_features ;
    decision_tree : decisionTree class features ;
    instance : featureSpace features
}.