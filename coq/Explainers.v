From RFXP Require Import Xp.


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