Require Import List ZArith PrimFloat.
Require Import Coq.Program.Equality Coq.Logic.ProofIrrelevance.
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

    Section StringEnumFeature.

        Import StringSet.

        (* Given a feature based on some enumeration of strings { s1, .., sn },
           there is a test for every subset of the enumeration: whether the
           feature value is a member of that subset *)
        Variant string_enum_test (s : StringSet.t) := subset_mem (p : string_enum s -> bool).

        Definition string_enum_feature (s : StringSet.t) : feature := {|
            dom := string_enum s ;
            testIndex := string_enum_test s ;
            tests := fun t x =>
                match t with
                | subset_mem _ p => p x
                end
        |}.

    End StringEnumFeature.


    (* TODO: include more features (ints?) *)
    (* TODO: abstract away the float and string stuff (modules??) *)
    Inductive getFeatureKind : feature -> Type :=
    | isContinuousFeature : getFeatureKind float_feature
    | isBooleanFeature : getFeatureKind boolean_feature
    | isStringEnumFeature (s : StringSet.t) : getFeatureKind (string_enum_feature s).

    Inductive featureSig : nat -> Type :=
    | featureSigNil : featureSig 0
    | featureSigCons {n : nat} (f : feature) (get : getFeatureKind f)
                     (fs : featureSig n) : featureSig (S n).

    Inductive featureVec : forall {n : nat}, featureSig n -> Type :=
    | featureVecNil : featureVec featureSigNil
    | featureVecCons (f : feature) (get : getFeatureKind f) (x : dom f)
                     {n : nat} {fs : featureSig n} (vs : featureVec fs) :
                        featureVec (featureSigCons f get fs).


    Definition feature_wrap : Type := { f : feature & getFeatureKind f }.
    Definition float_feature_wrap : feature_wrap := existT _ float_feature isContinuousFeature.
    Definition boolean_feature_wrap : feature_wrap := existT _ boolean_feature isBooleanFeature.
    Definition string_enum_feature_wrap (s : StringSet.t) : feature_wrap := existT _ (string_enum_feature s) (isStringEnumFeature s).


    Fixpoint getFeatureWrap {n : nat} (fs : featureSig n) {struct fs} : fin n -> feature_wrap :=
        match fs in featureSig n return fin n -> feature_wrap with
        | featureSigNil => fun i =>
            match i in fin 0 with
            end
        | featureSigCons f get fs => fun i =>
            match i in fin (S p) return (fin p -> feature_wrap) -> feature_wrap with
            | F1 => fun _ => existT _ f get
            | FS i => fun k => k i
            end (getFeatureWrap fs)
        end.

    Definition getFeature {n : nat} (fs : featureSig n) (i : fin n) : feature :=
        projT1 (getFeatureWrap fs i).

    Lemma getFeatureF1 {n : nat} (f : feature) (get : getFeatureKind f) (fs : featureSig n) :
        getFeature (featureSigCons f get fs) F1 = f.
    Proof. reflexivity. Qed.

    Lemma getFeatureFS {n : nat} (f : feature) (get : getFeatureKind f) (fs : featureSig n) (i : fin n) :
        getFeature (featureSigCons f get fs) (FS i) = getFeature fs i.
    Proof. reflexivity. Qed.


    Fixpoint getValueS {n : nat} {fs : featureSig n}
                       (vs : featureVec fs) : forall (i : fin n), { f : feature & dom f } :=
        match vs in @featureVec n fs return forall (i : fin n), { f : feature & dom f } with
        | featureVecNil => fun i =>
            match i in fin 0 with
            end
        | featureVecCons f get x vs => fun i =>
            match i in fin (S p)
                return (forall (i : fin p), { f : feature & dom f })
                    -> { f : feature & dom f }
            with
            | F1 => fun _ => existT _ f x
            | FS i => fun k => k i
            end (getValueS vs)
        end.

    Lemma getValueSF1 {n : nat} {fs : featureSig n}
                      (f : feature) (get : getFeatureKind f) (x : dom f) (vs : featureVec fs) :
        getValueS (featureVecCons f get x vs) F1 = existT _ f x.
    Proof. reflexivity. Qed.

    Lemma getValueSFS {n : nat} {fs : featureSig n}
                      (f : feature) (get : getFeatureKind f) (x : dom f) (vs : featureVec fs) (i : fin n) :
        getValueS (featureVecCons f get x vs) (FS i) = getValueS vs i.
    Proof. reflexivity. Qed.


    Definition getValue {n : nat} {fs : featureSig n} (vs : featureVec fs) (i : fin n) :
            dom (projT1 (getValueS vs i)) :=
        projT2 (getValueS vs i).

    Lemma getValueF1 {n : nat} {fs : featureSig n}
                     (f : feature) (get : getFeatureKind f) (x : dom f) (vs : featureVec fs) :
        getValue (featureVecCons f get x vs) F1 = x.
    Proof. reflexivity. Qed.

    Lemma getValueFS {n : nat} {fs : featureSig n}
                     (f : feature) (get : getFeatureKind f) (x : dom f) (vs : featureVec fs) (i : fin n) :
        getValue (featureVecCons f get x vs) (FS i) = getValue vs i.
    Proof. reflexivity. Qed.

    
    Definition featureTest {n : nat} {fs : featureSig n}
                           (vs : featureVec fs) (i : fin n)
                           (t : testIndex (projT1 (getValueS vs i))) : bool :=
        tests _ t (getValue vs i).


    (* We define below variants getValue' and featureTest' whose types are based on
       getFeature instead of getValueS. This is achieved by using equalities between
       types, which looks pretty advanced. I use proof irrelevance to solve some lemmas;
       I have not found a better solution. *)

    Lemma getValueS_Domain {n : nat} (fs : featureSig n) (vs : featureVec fs) (i : fin n) :
        projT1 (getValueS vs i) = getFeature fs i.
    Proof.
        induction vs as [| f get x n fs vs IH ]; try (now inversion i);
        dependent destruction i.
        -   now rewrite getValueSF1, getFeatureF1.
        -   now rewrite getValueSFS, getFeatureFS, IH.
    Qed.

    Definition getValue' {n : nat} {fs : featureSig n} (vs : featureVec fs) (i : fin n) :
        dom (getFeature fs i).
    Proof.
        rewrite <- getValueS_Domain with (vs := vs).
        exact (projT2 (getValueS vs i)).
    Defined.

    Lemma getValueF1' {n : nat} {fs : featureSig n}
                      (f : feature) (get : getFeatureKind f) (x : dom f) (vs : featureVec fs) :
        getValue' (featureVecCons f get x vs) F1 = x.
    Proof.
        unfold getValue';
        remember (getValueS_Domain (featureSigCons f get fs) (featureVecCons f get x vs) F1) as E;
        now rewrite <- Eqdep.Eq_rect_eq.eq_rect_eq with (h := E).
    Qed.

    Lemma getValueFS' {n : nat} {fs : featureSig n}
                      (f : feature) (get : getFeatureKind f) (x : dom f) (vs : featureVec fs) (i : fin n) :
        getValue' (featureVecCons f get x vs) (FS i) = getValue' vs i.
    Proof.
        unfold getValue';
        remember (getValueS_Domain fs vs i) as E;
        remember (getValueS_Domain (featureSigCons f get fs) (featureVecCons f get x vs) (FS i)) as E';
        replace E' with E; now try apply proof_irrelevance.
    Qed.


    Definition featureTest' {n : nat} {fs : featureSig n}
                            (vs : featureVec fs) (i : fin n)
                            (t : testIndex (getFeature fs i)) : bool :=
        tests _ t (getValue' vs i).

    Global Arguments featureVecCons {f} get x {n fs} vs.

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
            (featureSigCons (string_enum_feature s1) (isStringEnumFeature s1)
                (featureSigCons (string_enum_feature s2) (isStringEnumFeature s2)
                    featureSigNil)).

    Local Program Definition v : featureVec fs :=
        featureVecCons isContinuousFeature (exist _ 0.5 _)
            (featureVecCons (isStringEnumFeature s1) (exist _ "red" _)
                (featureVecCons (isStringEnumFeature s2) (exist _ "no" _)
                    featureVecNil)).
    Solve All Obligations with check_mem_string.


    Proposition check1_dom :
        getFeature fs F1 = float_feature.
    Proof. reflexivity. Qed.

    Proposition check2_dom :
        getFeature fs (FS F1) = string_enum_feature s1.
    Proof. reflexivity. Qed.

    Proposition check3_dom :
        getFeature fs (FS (FS F1)) = string_enum_feature s2.
    Proof. reflexivity. Qed.


    Proposition check1_val :
        proj1_sig (getValue v F1) = 0.5.
    Proof. reflexivity. Qed.

    Proposition check2_val :
        proj1_sig (getValue v (FS F1)) = "red".
    Proof. reflexivity. Qed.

    Proposition check3_val :
        proj1_sig (getValue v (FS (FS F1))) = "no".
    Proof. reflexivity. Qed.


    Definition is_lt_075 : float_test.
    Proof. refine (float_lt (exist _ 0.75 _)); reflexivity. Defined.

    Definition is_yellow : string_enum_test s1 :=
        subset_mem s1 (fun '(exist _ s _) => eqb s "yellow").
    Definition is_no : string_enum_test s2 :=
        subset_mem s2 (fun '(exist _ s _) => eqb s "no").

    Proposition check_test1 :
        featureTest v F1 is_lt_075 = true.
    Proof. reflexivity. Qed.

    Proposition check_test2 :
        featureTest v (FS F1) is_yellow = false.
    Proof. reflexivity. Qed.

    Proposition check_test3 :
        featureTest v (FS (FS F1)) is_no = true.
    Proof. reflexivity. Qed.


    Local Ltac check_getValue' :=
        repeat (try (now setoid_rewrite getValueF1'); setoid_rewrite getValueFS').

    Proposition check1_val' :
        proj1_sig (getValue' v F1) = 0.5.
    Proof. check_getValue'. Qed.

    Proposition check2_val' :
        proj1_sig (getValue' v (FS F1)) = "red".
    Proof. check_getValue'. Qed.

    Proposition check3_val' :
        proj1_sig (getValue' v (FS (FS F1))) = "no".
    Proof. check_getValue'. Qed.


    Local Ltac check_featureTest' :=
        unfold featureTest'; check_getValue'.

    Proposition check_test1' :
        featureTest' v F1 is_lt_075 = true.
    Proof. check_featureTest'. Qed.

    Proposition check_test2' :
        featureTest' v (FS F1) is_yellow = false.
    Proof. check_featureTest'. Qed.

    Proposition check_test3' :
        featureTest' v (FS (FS F1)) is_no = true.
    Proof. check_featureTest'. Qed.

End Examples.