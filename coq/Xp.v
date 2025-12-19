From RFXP Require Import Utils Features.

Section Explanations.

    Context {n : nat}.

    (* TODO use FinSet.t *)
    Definition finset := fin n -> bool.

    Definition compl (X : finset) : finset :=
        fun i => negb (X i).

    
    Context (fs : featureSig n).

    Definition equiv (X : finset) (v1 v2 : featureVec fs) : Prop :=
        forall (i : fin n), X i = true -> getValue' v1 i = getValue' v2 i.


    Context {K : Type} (k : featureVec fs -> K) (v : featureVec fs).

    Definition WCXp (X : finset) : Prop :=
        exists (v' : featureVec fs), equiv (compl X) v v' /\ k v <> k v'.

    Definition WAXp (X : finset) : Prop :=
        forall (v' : featureVec fs), equiv X v v' -> k v = k v'.

End Explanations.


Section ExplanationsFacts.

    Context {n : nat} {fs : featureSig n} {K : Type} (k : featureVec fs -> K) (v : featureVec fs).

    (* TODO monotonicity facts *)

    Theorem XpDual :
        forall (X : @finset n), ~ WCXp fs k v X <-> WAXp fs k v (compl X).
    Proof.
        intros X; split; intro H.
        -   intros v' Heq.
            cut (~ k v <> k v'). admit. (* TODO classifiers are decidable *)
            intro abs; apply H; exists v'; split; assumption.
        -   intros (v' & H1 & H2); apply H2, H, H1.
    Admitted.

    Theorem XpDual' :
        forall (X : @finset n), WCXp fs k v X -> ~ WAXp fs k v (compl X).
    Proof.
        intros X H abs; now rewrite <- XpDual in abs.
    Qed.

    (* Can't exhibit a WCXp witness in constructive logic *)
    Theorem XpDual'' :
        forall (X : @finset n), ~ WAXp fs k v (compl X) -> ~ ~ WCXp fs k v X.
    Proof.
        intros X H abs; apply H, XpDual, abs.
    Qed.

End ExplanationsFacts.