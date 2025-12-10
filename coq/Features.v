Require Import List ZArith PrimFloat.
Import ListNotations.

From RFXP Require Import Utils.

Section Features.

    Record feature : Type := mk_feature {
        dom : Type ;
        testIndex : Type ;
        tests : testIndex -> dom -> bool
    }.


    Section BooleanFeature.

        (* The only test for a Boolean feature is to check the Boolean value *)
        Variant boolean_test := bool_check.

        Definition boolean_feature : feature := {|
            dom := bool ;
            testIndex := boolean_test ;
            tests := fun 'bool_check b => b
        |}.

    End BooleanFeature.

    Section FloatFeature.

        (* Every test for a float is a strict comparison to some threshold value *)
        Variant float_test := float_lt (y : float_std).

        Definition float_feature : feature := {|
            dom := float_std ;
            testIndex := float_test ;
            tests := fun t '(exist _ x _) =>
                match t with
                | float_lt (exist _ y _) => (x <? y)%float
                end
        |}.

    End FloatFeature.

    Section EnumFeature.

        Import StringSet.

        (* Given a feature based on some enumeration of strings { s1, .., sn },
           there is a test for every subset of the enumeration: whether the
           feature value is a member of that subset *)
        Variant enum_test (s : StringSet.t) := subset_mem (p : enum s -> bool).

        Definition enum_feature (s : StringSet.t) : feature := {|
            dom := enum s ;
            testIndex := enum_test s ;
            tests := fun t x =>
                match t with
                | subset_mem _ p => p x
                end
        |}.

    End EnumFeature.


    (* TODO: include more features (ints?) *)
    (* TODO: abstract away the float and string stuff (modules??) *)
    Inductive getFeatureKind : feature -> Type :=
    | isContinuousFeature : getFeatureKind float_feature
    | isBooleanFeature : getFeatureKind boolean_feature
    | isCategoricalFeature (s : StringSet.t) : getFeatureKind (enum_feature s).

    Inductive featureSig : nat -> Type :=
    | featureSigNil : featureSig 0
    | featureSigCons {n : nat} (f : feature) (get : getFeatureKind f)
                     (fs : featureSig n) : featureSig (S n).

    Inductive featureVec : forall {n : nat}, featureSig n -> Type :=
    | featureVecNil : featureVec featureSigNil
    | featureVecCons {f : feature} (get : getFeatureKind f) (x : dom f)
                     {n : nat} {fs : featureSig n} (vs : featureVec fs) :
                        featureVec (featureSigCons f get fs).


    Definition feature_wrap : Type := { f : feature & getFeatureKind f }.
    Definition float_feature_wrap : feature_wrap := existT _ float_feature isContinuousFeature.
    Definition enum_feature_wrap (s : StringSet.t) : feature_wrap := existT _ (enum_feature s) (isCategoricalFeature s).


    Program Fixpoint getFeature {n : nat} (fs : featureSig n) (i : nat) :
            feature_wrap + { n <= i } :=
        match fs with
        | featureSigNil => inright _
        | featureSigCons f get fs =>
            match i with
            | 0 => inleft (existT _ f get)
            | S i =>
                match getFeature fs i with
                | inleft r => inleft r
                | inright _ => inright _
                end
            end
        end.
    Solve All Obligations with Lia.lia.

    Program Definition getFeatureWrapSane {n : nat} (fs : featureSig n) (i : nat) (p : i < n) :
            feature_wrap :=
        match getFeature fs i with
        | inleft r => r
        | inright _ => _
        end.
    Solve All Obligations with Lia.lia.

    Definition getFeatureSane {n : nat} (fs : featureSig n) (i : nat) (p : i < n) :
            feature :=
        projT1 (getFeatureWrapSane fs i p).


    Program Fixpoint getVector {n : nat} {fs : featureSig n}
                               (vs : featureVec fs) (i : nat) :
            { f : feature_wrap & dom (projT1 f) & getFeature fs i = inleft f } + { n <= i } :=
        match vs with
        | featureVecNil => inright _
        | @featureVecCons f get x _ _ vs =>
            match i with
            | 0 => inleft (existT2 _ _ (existT _ f get) x _)
            | S i =>
                match getVector vs i with
                | inleft (existT2 _ _ f _ _) => inleft (existT2 _ _ f _ _)
                | inright _ => inright _
                end
            end
        end.
    Obligation 4 of getVector. destruct (getFeature wildcard'2 i); now inversion X0. Defined.
    Solve Obligations with Lia.lia.

    (* drop the identity proof returned by getVector *)
    Definition getVectorValue {n : nat} {fs : featureSig n}
                              (vs : featureVec fs) (i : nat) :
            { f : feature_wrap & dom (projT1 f) } + { n <= i } :=
        match getVector vs i with
        | inleft (existT2 _ _ f x _) => inleft (existT _ f x)
        | inright p => inright p
        end.

    Definition getVectorValueSane {n : nat} {fs : featureSig n}
                                  (vs : featureVec fs) (i : nat) (p : i < n) :
            dom (getFeatureSane fs i p).
    Proof.
        destruct (getVector vs i) as [((f, get), x, E) |]; [| Lia.lia].
        unfold getFeatureSane, getFeatureWrapSane; rewrite E.
        exact x.
    Defined.


    Definition featureTest {n : nat} {fs : featureSig n}
                           (vs : featureVec fs) (i : nat) (p : i < n)
                           (t : testIndex (getFeatureSane fs i p)) : bool :=
        tests _ t (getVectorValueSane vs i p).

End Features.

Section Examples.

    Import String.
    Local Open Scope string_scope.
    Local Open Scope float_scope.

    Local Ltac check_mem_string :=
        do 10 (try (now apply add_1); try (now apply singleton_2); apply add_2).

    Local Definition s1 : StringSet.t :=
        StringSet.add "red" (StringSet.add "blue" (StringSet.singleton "yellow")).
    Local Definition s2 : StringSet.t :=
        StringSet.add "yes" (StringSet.singleton "no").

    Local Definition fs : featureSig 3 :=
        featureSigCons float_feature isContinuousFeature
            (featureSigCons (enum_feature s1) (isCategoricalFeature s1)
                (featureSigCons (enum_feature s2) (isCategoricalFeature s2)
                    featureSigNil)).

    Local Program Definition v : featureVec fs :=
        featureVecCons isContinuousFeature (exist _ 0.5 _)
            (featureVecCons (isCategoricalFeature s1) (exist _ "red" _)
                (featureVecCons (isCategoricalFeature s2) (exist _ "no" _)
                    featureVecNil)).
    Solve All Obligations with check_mem_string.


    Proposition check1 :
        exists r,
            getVectorValue v 0 = inleft r /\
            match r with
            | existT _ (existT _ f isContinuousFeature) x => proj1_sig x = 0.5
            | _ => False
            end.
    Proof. eexists; split; reflexivity. Qed.

    Proposition check2 :
        exists r,
            getVectorValue v 1 = inleft r /\
            match r with
            | existT _ (existT _ f (isCategoricalFeature s1)) x => proj1_sig x = "red"
            | _ => False
            end.
    Proof. eexists; split; reflexivity. Qed.

    Proposition check3 :
        exists r,
            getVectorValue v 2 = inleft r /\
            match r with
            | existT _ (existT _ f (isCategoricalFeature s2)) x => proj1_sig x = "no"
            | _ => False
            end.
    Proof. eexists; split; reflexivity. Qed.

    Proposition check1' :
        forall (p : 0 < 3), proj1_sig (getVectorValueSane v 0 p) = 0.5.
    Proof. reflexivity. Qed.

    Proposition check2' :
        forall (p : 1 < 3), proj1_sig (getVectorValueSane v 1 p) = "red".
    Proof. reflexivity. Qed.

    Proposition check3' :
        forall (p : 2 < 3), proj1_sig (getVectorValueSane v 2 p) = "no".
    Proof. reflexivity. Qed.

    Proposition check_test1 :
        forall (p : 0 < 3) (q : is_nan 0.75 = false),
            featureTest v 0 p (float_lt (exist _ 0.75 q)) = true.
    Proof. eexists; reflexivity. Qed.

    Proposition check_test2 :
        forall (p : 1 < 3),
            featureTest v 1 p (subset_mem s1 (fun '(exist _ s _) => eqb s "yellow")) = false.
    Proof. reflexivity. Qed.

    Proposition check_test3 :
        forall (p : 2 < 3),
            featureTest v 2 p (subset_mem s2 (fun '(exist _ s _) => eqb s "no")) = true.
    Proof. reflexivity. Qed.

End Examples.