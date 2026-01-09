Require Import Equalities Morphisms.

From RFXP Require Import Utils Features.


Module Type FeatureSig <: FinSig.
    Include FinSig.
    Parameter fs : featureSig n.

    Module N : FinSig
        with Definition n := n.
        Definition n := n.
    End N.

    Module Export Props := FinSetProperties N.
    Module S := Props.FS.

    Definition equiv (X : S.t) (v1 v2 : featureVec fs) : Prop :=
        forall (i : fin n), S.In i X -> getValue' v1 i = getValue' v2 i.

    Global Instance equiv_compat : Proper (S.Equal ==> Logic.eq ==> Logic.eq ==> iff) equiv.
    Proof.
        intros s1 s2 HEs v1 v1' HE1 v2 v2' HE2; subst v1' v2';
        split; intros H i Hi; apply H, HEs, Hi.
    Qed.

End FeatureSig.


Module Type Classifier (F : FeatureSig).
    Declare Module K : UsualDecidableType.

    Parameter t : Type.
    Parameter eval : t -> featureVec F.fs -> K.t.
End Classifier.

Module Type ClassifierInstance (F : FeatureSig) (C : Classifier F).
    Parameter k : C.t.
    Parameter v : featureVec F.fs.
End ClassifierInstance.

Module Type ExplanationProblem := FeatureSig <+ Classifier <+ ClassifierInstance.


Module Explanations (Export E : ExplanationProblem).

    Definition WCXp (X : S.t) : Prop :=
        exists (v' : featureVec fs), equiv (S.compl X) v v' /\ eval k v <> eval k v'.

    Definition WAXp (X : S.t) : Prop :=
        forall (v' : featureVec fs), equiv X v v' -> eval k v = eval k v'.

    Definition CXp (X : S.t) : Prop :=
        WCXp X /\ forall X', S.Subset X' X -> WCXp X' -> S.Equal X' X.

    Definition AXp (X : S.t) : Prop :=
        WAXp X /\ forall X', S.Subset X' X -> WAXp X' -> S.Equal X' X.


    Global Instance WCXp_compat : Proper (S.Equal ==> iff) WCXp.
    Proof.
        intros s1 s2 HEs; split; intros (v' & H1 & H2);
        exists v'; split; try (now rewrite <- ?HEs); now rewrite -> ?HEs.
    Qed.

    Global Instance WCXAp_compat : Proper (S.Equal ==> iff) WAXp.
    Proof.
        intros s1 s2 HEs; split; intros H v' HE; apply H;
        try (now rewrite HEs); now rewrite <- HEs.
    Qed.

End Explanations.


Module ExplanationsFacts (Export E : ExplanationProblem).

    Module Xp := Explanations E.
    Import Xp Props.


    (* Monotonicity *)

    Theorem WCXp_monotonic :
        forall (X1 X2 : S.t), S.Subset X1 X2 -> WCXp X1 -> WCXp X2.
    Proof.
        intros X1 X2 HSubs (v' & HEq & HDiff);
        exists v'; split; try (now apply HDiff);
        intros i Hi; apply Subset_compl in HSubs;
        now apply HEq, HSubs.
    Qed.

    Theorem WAXp_monotonic :
        forall (X1 X2 : S.t), S.Subset X1 X2 -> WAXp X1 -> WAXp X2.
    Proof.
        intros X1 X2 HSubs H v' HEq;
        apply H; intros x Hx; now apply HEq, HSubs.
    Qed.


    (* Sufficient conditions for minimality *)

    (* Same proof used twice; could be made more abstractly *)
    Theorem CXp_mono :
        forall (X : S.t),
            ( WCXp X /\ forall i, S.In i X -> ~ WCXp (S.remove i X) )
                -> CXp X.
    Proof.
        intros X (isWCXp & removeOneNotWCXp); split; try assumption;
        intros X' HSubs isWCXp'; apply subset_antisym; try assumption;
        intros i Hi; destruct (In_dec i X') as [| HN ]; try assumption;
        exfalso; apply removeOneNotWCXp with (i := i); try assumption;
        apply WCXp_monotonic with (X1 := X'); try assumption;
        intros j Hj; apply S.remove_spec; split; try (now apply HSubs);
        intro abs; now subst j.
    Qed.

    Theorem AXp_mono :
        forall (X : S.t),
            ( WAXp X /\ forall i, S.In i X -> ~ WAXp (S.remove i X) )
                -> AXp X.
    Proof.
        intros X (isWAXp & removeOneNotWAXp); split; try assumption;
        intros X' HSubs isWAXp'; apply subset_antisym; try assumption;
        intros i Hi; destruct (In_dec i X') as [| HN ]; try assumption;
        exfalso; apply removeOneNotWAXp with (i := i); try assumption;
        apply WAXp_monotonic with (X1 := X'); try assumption;
        intros j Hj; apply S.remove_spec; split; try (now apply HSubs);
        intro abs; now subst j.
    Qed.


    (* Duality *)

    Theorem XpDual_compl_of_not_WCXp_is_WAXp :
        forall (X : S.t), ~ WCXp X <-> WAXp (S.compl X).
    Proof.
        intros X; split; intro H.
        -   intros v' Heq;
            destruct (K.eq_dec (eval k v) (eval k v')); try assumption;
            exfalso; apply H; exists v'; split; assumption.
        -   intros (v' & H1 & H2); apply H2, H, H1.
    Qed.

    Theorem XpDual_compl_of_WCXp_is_not_WAXp :
        forall (X : S.t), WCXp X -> ~ WAXp (S.compl X).
    Proof.
        intros X H abs; now rewrite <- XpDual_compl_of_not_WCXp_is_WAXp in abs.
    Qed.

    (* Can't exhibit a WCXp witness in constructive logic *)
    Theorem XpDual_compl_of_WCXp_to_not_WAXp' :
        forall (X : S.t), ~ WAXp (S.compl X) -> ~ ~ WCXp X.
    Proof.
        intros X H abs; apply H, XpDual_compl_of_not_WCXp_is_WAXp, abs.
    Qed.

    Theorem XpDual_uncompl_of_not_WCXp_is_WAXp :
        forall (X : S.t), ~ WCXp (S.compl X) <-> WAXp X.
    Proof.
        intros X;
        assert (H := XpDual_compl_of_not_WCXp_is_WAXp (S.compl X));
        now rewrite compl_compl in H.
    Qed.

    Theorem XpDual_uncompl_of_WCXp_is_not_WAXp :
        forall (X : S.t), WCXp (S.compl X) -> ~ WAXp X.
    Proof.
        intros X H abs; now rewrite <- XpDual_uncompl_of_not_WCXp_is_WAXp in abs.
    Qed.

    Theorem XpDual_uncompl_of_WCXp_is_not_WAXp' :
        forall (X : S.t), ~ WAXp X -> ~ ~ WCXp (S.compl X).
    Proof.
        intros X H abs; apply H, XpDual_uncompl_of_not_WCXp_is_WAXp, abs.
    Qed.

End ExplanationsFacts.


Module Type Explainer (Export E : ExplanationProblem).

    Module Xp := Explanations E.

    Inductive isXp (X : S.t) : Type :=
    | isAXp : Xp.AXp X -> isXp X
    | isCXp : Xp.CXp X -> isXp X.

    Parameter getNew : list S.t -> S.t.

End Explainer.

Module Type CorrectExplainer (E : ExplanationProblem) <: Explainer E.

    Include Explainer E.

    Axiom getNewSound :
        forall Xs, isXp (getNew Xs).

    Axiom getNewComplete :
        forall Xs, List.In (getNew Xs) Xs ->
            forall X, isXp X -> List.In X Xs.

End CorrectExplainer.