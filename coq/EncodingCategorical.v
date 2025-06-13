Require Import List String Nat.
From RFXP Require Import Utils Features DT RF.

(* We define a function that take a decision tree on continuous and categorical
   features and computes an equivalent tree that is purely categorical. *)

Section EncodingCategoricalDefinition.

    Context (enums_strings : list StringSet.t).

    (* We'll assume no string in [enums_strings] starts with "__" to give ourselves
       a safe way to make more strings. *)
    (* Maybe not needed?
    Hypothesis enums_wf : forall (e : StringSet.t) (s s' : string),
        In e enums_strings ->
        StringSet.In s e ->
        s <> ("__" ++ s')%string.
    *)

    Context {n : nat} (fs : featureList n).

    Hypothesis fs_enum_or_float : enum_float_list enums_strings fs.

    Definition getKind (i : featureIndex n) : isEnumOrFloat _ (fs i) :=
        match fs_enum_or_float with
        | all_features _ _ get => get i
        end.

    (* Starting DT *)
    Parameter (rf : randomForest fs).


    Section MakeFloatFeaturesIntoEnums.

        (* With a first pass over the random forest, we collect all the thresholds
           that occur in continuous tests. *)

        Definition accByKind
            {i : featureIndex n}
            {ss : list StringSet.t}
            (k : isEnumOrFloat ss (fs i)) : Type :=
            match k with
            | left _ => unit
            | right _ => FloatSet.t
            end.

        Definition thresholds_collector : Type :=
            indexed (fun i:featureIndex n => accByKind (getKind i)).

        Definition init : thresholds_collector :=
            fun i:featureIndex n =>
                match getKind i as k return accByKind k with
                | left _ => tt
                | right _ => FloatSet.empty
                end.

        Definition add_threshold
            (i : featureIndex n)
            (f : float_std)
            (acc : thresholds_collector) : thresholds_collector :=
            fun j:featureIndex n =>
                acc j. (* ??? *)

    End MakeFloatFeaturesIntoEnums.


    (* TODO *)
    (* We add an enum domain for every continuous feature *)
    Parameter extend_ss : list StringSet.t.

    (* TODO *)
    Definition extend_fs : featureList n :=
        match fs_enum_or_float with
        | all_features _ _ enumOrFloat =>
            fun i =>
                match enumOrFloat i with
                | left _ => fs i
                | right _ => fs i (* TODO return new enum feature *)
                end
        end.


    (* TODO *)
    (* We translate the input DT into a categorical one *)
    Parameter make_categorical : decisionTree class extend_fs.

End EncodingCategoricalDefinition.