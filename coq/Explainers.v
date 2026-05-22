Require Import Bool.

From RFXP Require Import Utils Xp.

(* Base definitions *)

Module ExplainersDefs (Import E : InputProblem).
    Include ExplanationsDefs E.

End ExplainersDefs.

Module EnumeratorsDefs (Import E : InputProblem).
    Include ExplainersDefs E.

    Variant Xp : Type :=
    | isAXp (X : S.t) : Xp
    | isCXp (X : S.t) : Xp.

    Definition isXp (X : Xp) : Prop :=
        match X with
        | isAXp X => AXp X
        | isCXp X => CXp X
        end.

End EnumeratorsDefs.


(* Find minimal explanations from a seed (eliminate redundant features) *)

Module Type AXpFinderBase (Import E : InputProblem).
    Module Import Xp := ExplainersDefs E.

    Parameter findAXp : S.t -> S.t.
End AXpFinderBase.

Module Type AXpFinder (Import E : InputProblem).
    Include AXpFinderBase E.

    Axiom findAXpSound :
        forall X, Xp.WAXp X -> Xp.AXp (findAXp X).

    Axiom findAXpSane :
        forall X, S.Subset (findAXp X) X.

End AXpFinder.


Module Type CXpFinderBase (Import E : InputProblem).
    Module Import Xp := ExplainersDefs E.

    Parameter findCXp : S.t -> S.t.
End CXpFinderBase.

Module Type CXpFinder (Import E : InputProblem).
    Include CXpFinderBase E.

    Axiom findCXpSound :
        forall X, Xp.WCXp X -> Xp.CXp (findCXp X).

    Axiom findCXpSane :
        forall X, S.Subset (findCXp X) X.

End CXpFinder.


(* Decide if a set is a WCXp *)

Module Type WCXpCheckerBase (Import E : InputProblem).
    Module Import Xp := ExplainersDefs E.

    Parameter checkWCXp : S.t -> bool.
End WCXpCheckerBase.

Module Type WCXpChecker (Import E : InputProblem) <: WCXpCheckerBase E.
    Include WCXpCheckerBase E.

    Axiom checkWCXpSound :
        forall X, Bool.reflect (Xp.WCXp X) (checkWCXp X).

End WCXpChecker.


(* Default implementations of finders given a WCXp checker *)

Module AXpIterativeFinderBase (Import E : InputProblem) (Chk : WCXpChecker E) <: AXpFinderBase E.
    Module Import Xp := ExplainersDefs E.

    Local Definition checkWAXp X := negb (Chk.checkWCXp (S.compl X)).

    Definition findAXp := S.shrink checkWAXp.

End AXpIterativeFinderBase.

Module AXpIterativeFinder (Import E : InputProblem) (Chk : WCXpChecker E) : AXpFinder E.
    Module Impl := AXpIterativeFinderBase E Chk.
    Include Impl.

    Lemma checkWAXp_reflect :
        forall X, Bool.reflect (Xp.WAXp X) (checkWAXp X).
    Admitted.

    Lemma findAXp_isWAXp :
        forall X, Xp.WAXp X -> Xp.WAXp (findAXp X).
    Proof.
        intros X H;
        apply (Bool.reflect_iff _ _ (checkWAXp_reflect X)),
            S.shrink_spec2 in H;
        now destruct (checkWAXp_reflect (S.shrink checkWAXp X)).
    Qed.

    Theorem findAXpSound :
        forall X, Xp.WAXp X -> Xp.AXp (findAXp X).
    Proof.
        intros X H; unfold findAXp; split.
        -   now apply findAXp_isWAXp.
        -   intros Y HSubs HY;
            apply S.shrink_spec3 with (p := checkWAXp);
                try (now apply (Bool.reflect_iff _ _ (checkWAXp_reflect _)));
                assumption.
    Qed.

    Theorem findAXpSane :
        forall X, E.S.Subset (findAXp X) X.
    Proof. apply S.shrink_spec1. Qed.

End AXpIterativeFinder.


Module CXpIterativeFinderBase (Import E : InputProblem) (Chk : WCXpChecker E) <: CXpFinderBase E.
    Module Import Xp := ExplainersDefs E.

    Definition findCXp := S.shrink Chk.checkWCXp.

End CXpIterativeFinderBase.

Module CXpIterativeFinder (Import E : InputProblem) (Chk : WCXpChecker E) : CXpFinder E.
    Module Impl := CXpIterativeFinderBase E Chk.
    Include Impl.

    Lemma findCXp_isWCXp :
        forall X, Xp.WCXp X -> Xp.WCXp (findCXp X).
    Proof.
        intros X H;
        apply (Bool.reflect_iff _ _ (Chk.checkWCXpSound X)),
            S.shrink_spec2 in H;
        now destruct (Chk.checkWCXpSound (S.shrink Chk.checkWCXp X)).
    Qed.

    Theorem findCXpSound :
        forall X, Xp.WCXp X -> Xp.CXp (findCXp X).
    Proof.
        intros X H; unfold findCXp; split.
        -   now apply findCXp_isWCXp.
        -   intros Y HSubs HY;
            apply S.shrink_spec3 with (p := Chk.checkWCXp);
                try (now apply (Bool.reflect_iff _ _ (Chk.checkWCXpSound _)));
                assumption.
    Qed.

    Theorem findCXpSane :
        forall X, E.S.Subset (findCXp X) X.
    Proof. apply S.shrink_spec1. Qed.

End CXpIterativeFinder.


(* Enumerate all explanations *)

Module Type EnumeratorBase (Import E : InputProblem).
    Module Import Xp := EnumeratorsDefs E.

    Parameter getNew : list Xp -> option Xp.
End EnumeratorBase.

Module Type Enumerator (Import E : InputProblem) <: EnumeratorBase E.
    Include EnumeratorBase E.

    Axiom getNewSound :
        forall Xs X, getNew Xs = Some X -> Xp.isXp X.

    Axiom getNewComplete :
        forall Xs X, getNew Xs = None -> Xp.isXp X -> List.In X Xs.
            
End Enumerator.


Module DummyExplainer (Import E : InputProblem) : EnumeratorBase E.
    Module Import Xp := EnumeratorsDefs E.

    Definition getNew (l : list Xp) := Some (isAXp E.S.all).
End DummyExplainer.