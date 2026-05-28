From RFXP Require Import Utils Features DT Xp Explainers.

Require Import Floats.


Module Type DTExplanationProblem <: ExplanationProblem :=
    FeatureSig <+ Output <+ DTOn <+ ClassifierInstance.

Module Type DTInputProblem <: InputProblem.
    Include DTExplanationProblem.
    Declare Module S : FinSet with Definition n := n.
End DTInputProblem.


Section FeatureSpaceConstraint.

    Variant floatRange : Type :=
    | rangeUpperBound (b : float_std) : floatRange (* ]-inf; b[ *)
    | rangeLowerBound (a : float_std) : floatRange (* [a; +inf[ *)
    | rangeBounds (a b : float_std) : (proj1_sig a <? proj1_sig b)%float = true -> floatRange. (* [a; b[ where a < b *)

    Variant fConstraint : forall (f : feature), getFeatureKind f -> Type :=
    | fcEmptyBool : fConstraint boolean_feature isBooleanFeature
    | fcSingletonBool (b : bool) : fConstraint boolean_feature isBooleanFeature
    | fcFullBool : fConstraint boolean_feature isBooleanFeature

    | fcEmptyFloat : fConstraint float_feature isContinuousFeature
    | fcFullFloat : fConstraint float_feature isContinuousFeature
    | fcRange (r : floatRange) : fConstraint float_feature isContinuousFeature
    | fcSingletonFloat (x : float_std) : fConstraint float_feature isContinuousFeature
    
    | fcSEnum (s : StringSet.t) (p : StringSet.elt -> bool) : fConstraint (string_enum_feature s) (isStringEnumFeature s).

    Definition applyLSplit {f : feature} (t : testIndex f)
                           (get : getFeatureKind f) : fConstraint f get -> fConstraint f get :=
        match get in getFeatureKind f return testIndex f -> fConstraint f get -> fConstraint f get with
        | isContinuousFeature => fun t c =>
            match c in fConstraint _ isContinuousFeature return float_test -> fConstraint _ isContinuousFeature with
            | fcEmptyFloat => fun _ => fcEmptyFloat

            | fcFullFloat => fun '(float_lt x) => fcRange (rangeUpperBound x)

            | fcRange (rangeUpperBound b) => fun '(float_lt x) =>
                if (proj1_sig x <? proj1_sig b)%float then fcRange (rangeUpperBound x)
                else fcRange (rangeUpperBound b)

            | fcRange (rangeLowerBound a) => fun '(float_lt x) =>
                if (proj1_sig a <? proj1_sig x)%float then fcEmptyFloat
                else fcFullFloat (* TODO *)

            | fcRange (rangeBounds a b p) => fun _ => fcFullFloat (* TODO *)

            | fcSingletonFloat y => fun '(float_lt x) =>
                if (proj1_sig y <? proj1_sig x)%float then fcSingletonFloat y
                else fcEmptyFloat
            end t

        | _ => fun t c => c (* TODO *)
        end t.

    Definition applyRSplit {f : feature} (t : testIndex f)
                           (get : getFeatureKind f) : fConstraint f get -> fConstraint f get :=
        match get in getFeatureKind f return testIndex f -> fConstraint f get -> fConstraint f get with
        (* TODO *)
        | _ => fun t c => c
        end t.

    Program Definition getWitness {f : feature} (get : getFeatureKind f) : fConstraint f get -> option (dom f) :=
        match get in getFeatureKind f return fConstraint f _ -> option (dom f) with
        | isBooleanFeature => fun c =>
            match c with
            | fcEmptyBool => None
            | fcSingletonBool b => Some b
            | fcFullBool => Some true
            | _ => False_rect _ _
            end
        | isContinuousFeature => fun c =>
            match c with
            | fcEmptyFloat => None
            | fcFullFloat => Some (exist _ 0.0 _)%float
            | fcSingletonFloat x => Some x
            | fcRange (rangeLowerBound a) => Some (exist _ (a + 1.0) _)%float
            | fcRange (rangeUpperBound a) => Some (exist _ (a - 1.0) _)%float
            | fcRange (rangeBounds a b p) => Some (exist _ ((a + b) / 2.0) _)%float
            | _ => False_rect _ _
            end
        | isStringEnumFeature s => fun c =>
            match c with
            | fcSEnum s p =>
                match StringSet.choose (StringSet.filter p s) with
                | None => None
                | Some e => Some (exist _ e _)
                end
            | _ => False_rect _ _
            end
        end.
    Admit Obligations.


    Inductive featureSpaceConstraint : forall {n : nat}, featureSig n -> Type :=
    | featureSpaceConstraintNil : featureSpaceConstraint featureSigNil
    | featureSpaceConstraintCons
        (f : feature) (get : getFeatureKind f) (c : fConstraint f get)
        {n : nat} {fs : featureSig n} (cs : featureSpaceConstraint fs) :
            featureSpaceConstraint (featureSigCons f get fs).

    (* HERE BE DRAGONS *)
    Local Fixpoint mapOne {n : nat} {fs : featureSig n}
                          (cs : featureSpaceConstraint fs) {struct cs} :
                            forall (i : fin n),
                                (forall (get : getFeatureKind (getFeature fs i)),
                                    fConstraint (getFeature fs i) get -> fConstraint (getFeature fs i) get) ->
                                featureSpaceConstraint fs :=
        match cs in @featureSpaceConstraint n fs
                 return forall {i : fin n},
                            (forall (get : getFeatureKind (getFeature fs i)),
                                fConstraint (getFeature fs i) get -> fConstraint (getFeature fs i) get) ->
                            featureSpaceConstraint fs with
        | featureSpaceConstraintNil =>
            fun _ _ => featureSpaceConstraintNil
        | @featureSpaceConstraintCons f get c _ fs cs =>
            fun i =>
                match i in fin (S p)
                      return forall (fs : featureSig p) (cs : featureSpaceConstraint fs),
                        (forall (j : fin p),
                            (forall (get : getFeatureKind (getFeature fs j)),
                                fConstraint (getFeature fs j) get -> fConstraint (getFeature fs j) get) ->
                            featureSpaceConstraint fs) ->
                        (forall (get' : getFeatureKind (getFeature (featureSigCons f get fs) i)),
                            fConstraint (getFeature (featureSigCons f get fs) i) get' ->
                            fConstraint (getFeature (featureSigCons f get fs) i) get') ->
                        featureSpaceConstraint (featureSigCons f get fs) with
                | F1 => fun fs cs _ ap => featureSpaceConstraintCons f get (ap get c) cs
                | FS i => fun fs cs k ap => featureSpaceConstraintCons f get c (k i ap)
                end fs cs (mapOne cs)
        end.

    Definition splitFSConstraintLeft {n : nat} {fs : featureSig n} (i : fin n) (t : testIndex (getFeature fs i)) :
            featureSpaceConstraint fs -> featureSpaceConstraint fs :=
        fun cs => mapOne cs i (applyLSplit t).

    Definition splitFSConstraintRight {n : nat} {fs : featureSig n} (i : fin n) (t : testIndex (getFeature fs i)) :
            featureSpaceConstraint fs -> featureSpaceConstraint fs :=
        fun cs => mapOne cs i (applyRSplit t).

    Fixpoint witness {n : nat} {fs : featureSig n} (cs : featureSpaceConstraint fs) : option (featureVec fs) :=
        match cs with
        | featureSpaceConstraintNil => Some (featureVecNil)
        | featureSpaceConstraintCons f get c cs =>
            match getWitness get c with
            | None => None
            | Some x =>
                match witness cs with
                | None => None
                | Some vs => Some (featureVecCons get x vs)
                end
            end
        end.

    Fixpoint initConstraint {n : nat} (X : fin n -> bool) {fs : featureSig n} (vs : featureVec fs) : featureSpaceConstraint fs :=
        match vs in @featureVec n fs return (fin n -> bool) -> featureSpaceConstraint fs with
        | featureVecNil => fun _ => featureSpaceConstraintNil
        | @featureVecCons f get x _ fs vs => fun X =>
            let c : fConstraint f get :=
                match get with
                | isBooleanFeature => fcFullBool
                | isContinuousFeature => fcFullFloat
                | isStringEnumFeature s => fcSEnum s (fun _ => true)
                end
            in
            featureSpaceConstraintCons f get c (initConstraint (fun k => X (FS k)) vs)
        end X.

End FeatureSpaceConstraint.


Module DtWCXpCheckerImpl (C : DT) (S : FinSet with Definition n := C.n).
    Module Import FD := FeatureSigDefs C S.

    Fixpoint refute_aux
            (v : featureVec C.fs)
            (c0 : C.K.t)
            (X : S.t)
            (C : featureSpaceConstraint C.fs)
            (dt : C.t)
            : option (featureVec C.fs) :=
        match dt with
        | Leaf c =>
            if C.K.eq_dec c c0 then
                None
            else
                witness C
        | Node i test dt1 dt2 =>
            if S.mem i X then
                match refute_aux v c0 X (splitFSConstraintLeft i test C) dt1 with
                | Some r => Some r
                | None => refute_aux v c0 X (splitFSConstraintRight i test C) dt2
                end
            else
                let dt' :=
                    if featureTest' v i test then dt1
                    else dt2
                in
                refute_aux v c0 X C dt'
        end.

    Definition init : S.t -> featureVec C.fs -> featureSpaceConstraint C.fs :=
        fun X => initConstraint (fun i => S.mem i X).

    (* Search for a v' that gives a different prediction than v on the decision tree
       and such that v' agrees with v on the complement of X. *)
    Definition refute (dt : C.t) (v : featureVec C.fs) (X : S.t) : option (featureVec C.fs) :=
        refute_aux v (C.eval dt v) X (init X v) dt.

    Theorem refute_success_agrees :
        forall (dt : C.t) (v v' : featureVec C.fs) (X : S.t),
            refute dt v X = Some v' -> FD.equiv (S.compl X) v v'.
    Admitted.

    Theorem refute_success_contradicts :
        forall (dt : C.t) (v v' : featureVec C.fs) (X : S.t),
            refute dt v X = Some v' -> ~ C.K.eq (C.eval dt v) (C.eval dt v').
    Admitted.

    Theorem refute_fail :
        forall (dt : C.t) (v v' : featureVec C.fs) (X : S.t),
            refute dt v X = None -> FD.equiv (S.compl X) v v' -> C.K.eq (C.eval dt v) (C.eval dt v').
    Admitted.

End DtWCXpCheckerImpl.


Module DtWCXpChecker (Import E_ : DTInputProblem) : WCXpChecker with Module E := E_.
    Module E := E_.
    Module Import Xp := ExplainersDefs E.
    Module Impl := DtWCXpCheckerImpl E E.S.

    Definition checkWCXp (X : S.t) :=
        match Impl.refute E.k E.v X with
        | None => false
        | Some _ => true
        end.

    Theorem checkWCXpSound :
        forall X, Bool.reflect (Xp.WCXp X) (checkWCXp X).
    Proof.
        intros X; unfold checkWCXp;
        destruct (Impl.refute E.k E.v X) as [v |] eqn:Heq;
        constructor.
        -   exists v; split.
            +   eapply Impl.refute_success_agrees; eassumption.
            +   eapply Impl.refute_success_contradicts; eassumption.
        -   intros (v & Heqv & Hcont);
            eapply Hcont, Impl.refute_fail; eassumption.
    Qed.

End DtWCXpChecker.


Module DtAXpFinder (E_ : DTInputProblem) : AXpFinder with Module E := E_.
    Module Chk := DtWCXpChecker E_.
    Module Impl := AXpIterativeFinder E_ Chk.
    Include Impl.
End DtAXpFinder.

Module DtCXpFinder (E_ : DTInputProblem) : CXpFinder with Module E := E_.
    Module Chk := DtWCXpChecker E_.
    Module Impl := CXpIterativeFinder E_ Chk.
    Include Impl.
End DtCXpFinder.