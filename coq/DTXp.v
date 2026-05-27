From RFXP Require Import Utils Features DT Xp Explainers.


Module Type DTExplanationProblem <: ExplanationProblem :=
    FeatureSig <+ Output <+ DTOn <+ ClassifierInstance.

Module Type DTInputProblem <: InputProblem.
    Include DTExplanationProblem.
    Declare Module S : FinSet with Definition n := n.
End DTInputProblem.


Module DtWCXpCheckerImpl (C : DT) (S : FinSet with Definition n := C.n).

    Parameter constraint : Type.
    Parameter init : S.t -> constraint.
    Parameter update : forall {i : fin C.n}, testIndex (getFeature C.fs i) -> constraint -> constraint.
    Parameter nupdate : forall {i : fin C.n}, testIndex (getFeature C.fs i) -> constraint -> constraint.
    Parameter witness : constraint -> option (featureVec C.fs).

    Fixpoint refute
            (v : featureVec C.fs)
            (c0 : C.K.t)
            (X : S.t)
            (C : constraint)
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
                match refute v c0 X (update test C) dt1 with
                | Some r => Some r
                | None => refute v c0 X (nupdate test C) dt2
                end
            else
                let dt' :=
                    if featureTest' v i test then dt1
                    else dt2
                in
                refute v c0 X C dt'
        end.

End DtWCXpCheckerImpl.


Module DtWCXpChecker (Import E_ : DTInputProblem) : WCXpChecker with Module E := E_.
    Module E := E_.
    Module Import Xp := ExplainersDefs E.
    Module Impl := DtWCXpCheckerImpl E E.S.

    Definition checkWCXp (X : S.t) :=
        match Impl.refute E.v (E.eval E.k E.v) X (Impl.init X) E.k with
        | None => true
        | Some _ => false
        end.

    Theorem checkWCXpSound :
        forall X, Bool.reflect (Xp.WCXp X) (checkWCXp X).
    Admitted.

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