From RFXP Require Import Utils Features DT RF.

(* We define a function that take a decision tree on continuous and categorical
   features and computes an equivalent tree that is purely categorical. *)

Section EncodingCategoricalDefinition.

    Context (class : Type) {n : nat} (fs : featureList n).

    Context (ss : list StringSet.t).
    Hypothesis fs_enum_or_float : enum_float_list ss fs.

    (* Starting DT *)
    Parameter (dt : decisionTree class fs).

    (* TODO *)
    (* We add an enum domain for every continuous feature *)
    Parameter ss' : StringSet.t.

    (* TODO *)
    Parameter fs' : featureList n.

    (* TODO *)
    (* We translate the input DT into a categorical one *)
    Parameter dt' : decisionTree class fs'.

End EncodingCategoricalDefinition.