Require Import Morphisms.

From RFXP Require Import Utils Features.

Module Explanations (F : FeatureSig).

    Module Props := FinSetProperties F.
    Module S := Props.FS.
    Export Props.
    

    Section ExplanationsMainDefs.

        Definition equiv (X : S.t) (v1 v2 : featureVec F.fs) : Prop :=
            forall (i : fin F.n), S.In i X -> getValue' v1 i = getValue' v2 i.

        Context {K : Type} (k : featureVec F.fs -> K) (v : featureVec F.fs).

        Definition WCXp (X : S.t) : Prop :=
            exists (v' : featureVec F.fs), equiv (S.compl X) v v' /\ k v <> k v'.

        Definition WAXp (X : S.t) : Prop :=
            forall (v' : featureVec F.fs), equiv X v v' -> k v = k v'.

        Definition CXp (X : S.t) : Prop :=
            WCXp X /\ forall X', S.Subset X' X -> WCXp X' -> S.Equal X' X.

        Definition AXp (X : S.t) : Prop :=
            WAXp X /\ forall X', S.Subset X' X -> WAXp X' -> S.Equal X' X.

    End ExplanationsMainDefs.


    Global Instance equiv_compat : Proper (S.Equal ==> Logic.eq ==> Logic.eq ==> iff) equiv.
    Proof.
        intros s1 s2 HEs v1 v1' HE1 v2 v2' HE2; subst v1' v2';
        split; intros H i Hi; apply H, HEs, Hi.
    Qed.

    Global Instance WCXp_compat {K : Type} : Proper (Logic.eq ==> Logic.eq ==> S.Equal ==> iff) (@WCXp K).
    Proof.
        intros k1 k2 HEk v1 v2 HEv s1 s2 HEs; split; intros (v' & H1 & H2);
        subst k2 v2; exists v'; split; try (now rewrite <- ?HEs); now rewrite -> ?HEs.
    Qed.

    Global Instance WCXAp_compat {K : Type} : Proper (Logic.eq ==> Logic.eq ==> S.Equal ==> iff) (@WAXp K).
    Proof.
        intros k1 k2 HEk v1 v2 HEv s1 s2 HEs; split; intros H v' HE.
        -   subst k2 v2; apply H; now rewrite HEs.
        -   subst k2 v2; apply H; now rewrite <- HEs.
    Qed.

End Explanations.


Module ExplanationsFacts (F : FeatureSig).

    Module Xp := Explanations F.
    Import Xp Props.

    Section Facts.

        (* Monotonicity *)

        Context {K : Type} (k : featureVec F.fs -> K) (v : featureVec F.fs).

        Theorem WCXp_monotonic :
            forall (X1 X2 : S.t), S.Subset X1 X2 -> WCXp k v X1 -> WCXp k v X2.
        Proof.
            intros X1 X2 HSubs (v' & HEq & HDiff);
            exists v'; split; try (now apply HDiff);
            intros i Hi; apply Subset_compl in HSubs;
            now apply HEq, HSubs.
        Qed.

        Theorem WAXp_monotonic :
            forall (X1 X2 : S.t), S.Subset X1 X2 -> WAXp k v X1 -> WAXp k v X2.
        Proof.
            intros X1 X2 HSubs H v' HEq;
            apply H; intros x Hx; now apply HEq, HSubs.
        Qed.


        (* Sufficient conditions for minimality *)

        (* Same proof used twice; could be made more abstractly *)
        Theorem CXp_mono :
            forall (X : S.t),
                ( WCXp k v X /\ forall i, S.In i X -> ~ WCXp k v (S.remove i X) )
                    -> CXp k v X.
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
                ( WAXp k v X /\ forall i, S.In i X -> ~ WAXp k v (S.remove i X) )
                    -> AXp k v X.
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

        Hypothesis K_dec : forall (c c' : K), { c = c' } + { c <> c' }.

        Theorem XpDual_compl_of_not_WCXp_is_WAXp :
            forall (X : S.t), ~ WCXp k v X <-> WAXp k v (S.compl X).
        Proof.
            intros X; split; intro H.
            -   intros v' Heq.
                destruct (K_dec (k v) (k v')); try assumption;
                exfalso; apply H; exists v'; split; assumption.
            -   intros (v' & H1 & H2); apply H2, H, H1.
        Qed.

        Theorem XpDual_compl_of_WCXp_is_not_WAXp :
            forall (X : S.t), WCXp k v X -> ~ WAXp k v (S.compl X).
        Proof.
            intros X H abs; now rewrite <- XpDual_compl_of_not_WCXp_is_WAXp in abs.
        Qed.

        (* Can't exhibit a WCXp witness in constructive logic *)
        Theorem XpDual_compl_of_WCXp_to_not_WAXp' :
            forall (X : S.t), ~ WAXp k v (S.compl X) -> ~ ~ WCXp k v X.
        Proof.
            intros X H abs; apply H, XpDual_compl_of_not_WCXp_is_WAXp, abs.
        Qed.

        Theorem XpDual_uncompl_of_not_WCXp_is_WAXp :
            forall (X : S.t), ~ WCXp k v (S.compl X) <-> WAXp k v X.
        Proof.
            intros X;
            assert (H := XpDual_compl_of_not_WCXp_is_WAXp (S.compl X));
            now rewrite compl_compl in H.
        Qed.

        Theorem XpDual_uncompl_of_WCXp_is_not_WAXp :
            forall (X : S.t), WCXp k v (S.compl X) -> ~ WAXp k v X.
        Proof.
            intros X H abs; now rewrite <- XpDual_uncompl_of_not_WCXp_is_WAXp in abs.
        Qed.

        Theorem XpDual_uncompl_of_WCXp_is_not_WAXp' :
            forall (X : S.t), ~ WAXp k v X -> ~ ~ WCXp k v (S.compl X).
        Proof.
            intros X H abs; apply H, XpDual_uncompl_of_not_WCXp_is_WAXp, abs.
        Qed.

    End Facts.

End ExplanationsFacts.