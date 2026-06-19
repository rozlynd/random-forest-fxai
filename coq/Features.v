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
        Variant string_enum_test (s : StringSet.t) := subset_mem (p : StringSet.elt -> bool).

        Definition string_enum_feature (s : StringSet.t) : feature := {|
            dom := string_enum s ;
            testIndex := string_enum_test s ;
            tests := fun t x =>
                match t with
                | subset_mem _ p => p (proj1_sig x)
                end
        |}.

    End StringEnumFeature.

    Section EnumFeature.

        Variable n : nat.

        Variant enum_test := enum_mem (p : fin n -> bool).

        Definition enum_feature : feature := {|
            dom := fin n ;
            testIndex := enum_test ;
            tests := fun t x =>
                match t with
                | enum_mem p => p x
                end
        |}.

    End EnumFeature.


    Variant featureKind :=
    | isContinuousFeature
    | isBooleanFeature
    | isStringEnumFeature (s : StringSet.t).

    Definition getf (f : featureKind) : feature :=
        match f with
        | isContinuousFeature => float_feature
        | isBooleanFeature => boolean_feature
        | isStringEnumFeature s => string_enum_feature s
        end.

    Inductive featureSig : nat -> Type :=
    | featureSigNil : featureSig 0
    | featureSigCons {n : nat} (f : featureKind)
                     (fs : featureSig n) : featureSig (S n).

    Inductive featureVec : forall {n : nat}, featureSig n -> Type :=
    | featureVecNil : featureVec featureSigNil
    | featureVecCons (f : featureKind) (x : dom (getf f))
                     {n : nat} {fs : featureSig n} (vs : featureVec fs) :
                        featureVec (featureSigCons f fs).


    Fixpoint getFeatureKind {n : nat} (fs : featureSig n) {struct fs} : fin n -> featureKind :=
        match fs in featureSig n return fin n -> featureKind with
        | featureSigNil => fun i =>
            match i in fin 0 with
            end
        | featureSigCons f fs => fun i =>
            match i in fin (S p) return (fin p -> featureKind) -> featureKind with
            | F1 => fun _ => f
            | FS i => fun k => k i
            end (getFeatureKind fs)
        end.

    Definition getFeature {n : nat} (fs : featureSig n) (i : fin n) : feature :=
        getf (getFeatureKind fs i).

    Lemma getFeatureF1 {n : nat} (f : featureKind) (fs : featureSig n) :
        getFeature (featureSigCons f fs) F1 = getf f.
    Proof. reflexivity. Qed.

    Lemma getFeatureFS {n : nat} (f : featureKind) (fs : featureSig n) (i : fin n) :
        getFeature (featureSigCons f fs) (FS i) = getFeature fs i.
    Proof. reflexivity. Qed.


    Fixpoint getValueS {n : nat} {fs : featureSig n}
                       (vs : featureVec fs) : forall (i : fin n), { f : feature & dom f } :=
        match vs in @featureVec n fs return forall (i : fin n), { f : feature & dom f } with
        | featureVecNil => fun i =>
            match i in fin 0 with
            end
        | featureVecCons f x vs => fun i =>
            match i in fin (S p)
                return (forall (i : fin p), { f : feature & dom f })
                    -> { f : feature & dom f }
            with
            | F1 => fun _ => existT _ (getf f) x
            | FS i => fun k => k i
            end (getValueS vs)
        end.

    Lemma getValueSF1 {n : nat} {fs : featureSig n}
                      (f : featureKind) (x : dom (getf f)) (vs : featureVec fs) :
        getValueS (featureVecCons f x vs) F1 = existT _ (getf f) x.
    Proof. reflexivity. Qed.

    Lemma getValueSFS {n : nat} {fs : featureSig n}
                      (f : featureKind) (x : dom (getf f)) (vs : featureVec fs) (i : fin n) :
        getValueS (featureVecCons f x vs) (FS i) = getValueS vs i.
    Proof. reflexivity. Qed.


    Definition getValue {n : nat} {fs : featureSig n} (vs : featureVec fs) (i : fin n) :
            dom (projT1 (getValueS vs i)) :=
        projT2 (getValueS vs i).

    Lemma getValueF1 {n : nat} {fs : featureSig n}
                     (f : featureKind) (x : dom (getf f)) (vs : featureVec fs) :
        getValue (featureVecCons f x vs) F1 = x.
    Proof. reflexivity. Qed.

    Lemma getValueFS {n : nat} {fs : featureSig n}
                     (f : featureKind) (x : dom (getf f)) (vs : featureVec fs) (i : fin n) :
        getValue (featureVecCons f x vs) (FS i) = getValue vs i.
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
        induction vs as [| f x n fs vs IH ]; try (now inversion i);
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
                      (f : featureKind) (x : dom (getf f)) (vs : featureVec fs) :
        getValue' (featureVecCons f x vs) F1 = x.
    Proof.
        unfold getValue';
        remember (getValueS_Domain (featureSigCons f fs) (featureVecCons f x vs) F1) as E;
        now rewrite <- Eqdep.Eq_rect_eq.eq_rect_eq with (h := E).
    Qed.

    Lemma getValueFS' {n : nat} {fs : featureSig n}
                      (f : featureKind) (x : dom (getf f)) (vs : featureVec fs) (i : fin n) :
        getValue' (featureVecCons f x vs) (FS i) = getValue' vs i.
    Proof.
        unfold getValue';
        remember (getValueS_Domain fs vs i) as E;
        remember (getValueS_Domain (featureSigCons f fs) (featureVecCons f x vs) (FS i)) as E';
        replace E' with E; now try apply proof_irrelevance.
    Qed.


    Definition featureTest' {n : nat} {fs : featureSig n}
                            (vs : featureVec fs) (i : fin n)
                            (t : testIndex (getFeature fs i)) : bool :=
        tests _ t (getValue' vs i).

    Global Arguments featureVecCons f x {n fs} vs.

End Features.


Section Examples.

    Import String.
    (*Import StringSetMoreProperties.*)
    Local Open Scope string_scope.
    Local Open Scope float_scope.

    Local Ltac check_mem_string :=
        do 10 (try (now apply add_1); try (now apply singleton_2); apply add_2).

    Local Definition s1 : StringSet.t :=
        StringSet.add "red" (StringSet.add "blue" (StringSet.singleton "yellow")).
    Local Definition s2 : StringSet.t :=
        StringSet.add "yes" (StringSet.singleton "no").

    Local Definition fs : featureSig 3 :=
        featureSigCons isContinuousFeature
            (featureSigCons (isStringEnumFeature s1)
                (featureSigCons (isStringEnumFeature s2)
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
        subset_mem s1 (fun s => eqb s "yellow").
    Definition is_no : string_enum_test s2 :=
        subset_mem s2 (fun s => eqb s "no").

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