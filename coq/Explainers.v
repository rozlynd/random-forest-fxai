Require Import Bool.

From RFXP Require Import Utils Xp.

(* Base definitions *)

Module ExplainersDefs (Import E : InputProblem).

    Include ExplanationsDefs E.

    Variant Xp : Type :=
    | isAXp (X : S.t) : Xp
    | isCXp (X : S.t) : Xp.

    Definition isXp (X : Xp) : Prop :=
        match X with
        | isAXp X => AXp X
        | isCXp X => CXp X
        end.

End ExplainersDefs.


(* Find minimal explanations from a seed (eliminate redundant features) *)

Module Type AXpFinder (E : InputProblem).
    Module Import Xp := ExplainersDefs E.

    Parameter findAXp : E.S.t -> E.S.t.
End AXpFinder.

Module Type SoundAXpFinder (E : InputProblem) <: AXpFinder E.
    Include AXpFinder E.

    Axiom findAXpSound :
        forall X, Xp.WAXp X -> Xp.AXp (findAXp X).

    Axiom findAXpSane :
        forall X, E.S.Subset (findAXp X) X.

End SoundAXpFinder.


Module Type CXpFinder (E : InputProblem).
    Module Import Xp := ExplainersDefs E.

    Parameter findCXp : E.S.t -> E.S.t.
End CXpFinder.

Module Type SoundCXpFinder (E : InputProblem) <: CXpFinder E.
    Include CXpFinder E.

    Axiom findCXpSound :
        forall X, Xp.WCXp X -> Xp.CXp (findCXp X).

    Axiom findCXpSane :
        forall X, E.S.Subset (findCXp X) X.

End SoundCXpFinder.


(* Decide if a set is a WCXp *)

Module Type WCXpChecker (E : InputProblem).
    Module Import Xp := ExplainersDefs E.

    Parameter checkWCXp : E.S.t -> bool.
End WCXpChecker.

Module Type SoundWCXpChecker (E : InputProblem) <: WCXpChecker E.
    Include WCXpChecker E.

    Axiom checkWCXpSound :
        forall X, Bool.reflect (Xp.WCXp X) (checkWCXp X).

End SoundWCXpChecker.


Module AXpIterativeFinder (Import E : InputProblem) (Chk : WCXpChecker E) <: AXpFinder E.
    Module Import Xp := ExplainersDefs E.

    Local Definition checkWAXp X := negb (Chk.checkWCXp (S.compl X)).

    Definition findAXp := S.shrink checkWAXp.

End AXpIterativeFinder.

Module SoundAXpIterativeFinder (Import E : InputProblem) (Chk : SoundWCXpChecker E) : SoundAXpFinder E.
    Module Impl := AXpIterativeFinder E Chk.
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

End SoundAXpIterativeFinder.


(* Enumerate all explanations *)

Module Type Explainer (E : InputProblem).
    Module Import Xp := ExplainersDefs E.

    Parameter getNew : list Xp -> option Xp.
End Explainer.

Module Type SoundExplainer (E : InputProblem) <: Explainer E.
    Include Explainer E.

    Axiom getNewSound :
        forall Xs X, getNew Xs = Some X -> Xp.isXp X.

End SoundExplainer.

Module Type CorrectExplainer (E : InputProblem) <: SoundExplainer E.
    Include SoundExplainer E.

    Axiom getNewComplete :
        forall Xs X, getNew Xs = None -> Xp.isXp X -> List.In X Xs.
            
End CorrectExplainer.


Module DummyExplainer (E : InputProblem) : Explainer E.
    Module Import Xp := ExplainersDefs E.

    Definition getNew (l : list Xp) := Some (isAXp E.S.all).
End DummyExplainer.