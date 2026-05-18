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


Module AXpIterativeFinder (Import E : InputProblem) (Chk : WCXpChecker E) : AXpFinder E.
    Module Import Xp := ExplainersDefs E.

    Program Fixpoint findAXp_aux (X : S.t) (i : nat) : S.t + { S.n < i } :=
        match i with
        | 0 => inleft X
        | S i =>
            match @to_fin S.n i with
            | inleft k =>
                let X' :=
                    let X' := S.remove k X in
                    if S.mem k X && negb (Chk.checkWCXp (S.compl X')) then
                        X'
                    else
                        X
                in
                match findAXp_aux X' i with
                | inleft R => inleft R
                | inright _ => inright _
                end
            | inright _ => inright _
            end
        end.
    Solve All Obligations with Lia.lia.

    Program Definition findAXp X :=
        match findAXp_aux X S.n with
        | inleft R => R
        | inright _ => False_rect _ _
        end.
    Solve All Obligations with Lia.lia.

End AXpIterativeFinder.

Module SoundAXpIterativeFinder (E : InputProblem) (Chk : SoundWCXpChecker E) : SoundAXpFinder E.
    Module Impl := AXpIterativeFinder E Chk.
    Include Impl.

    Theorem findAXpSound :
        forall X, Xp.WAXp X -> Xp.AXp (findAXp X).
    Admitted.

    Theorem findAXpSane :
        forall X, E.S.Subset (findAXp X) X.
    Admitted.

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