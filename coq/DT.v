Require Import List Equalities.
Import ListNotations.

From RFXP Require Import Utils Features Xp.

Section DTDef.

    Context {n : nat} (fs : featureSig n) (K : Type).

    Inductive dt : Type :=
    | Leaf (c : K)
    | Node (i : fin n)
           (_ : testIndex (getFeature  fs i))
           (dt1 dt2 : dt).

End DTDef.

Arguments Leaf {n fs K}.
Arguments Node {n fs K}.


Module DTOn (F' : FeatureSig) (K' : UsualDecidableType) <: Classifier
    with Module F := F'
    with Module K := K'.

    Module F := F'.
    Module K := K'.

    Definition t := dt F.fs K.t.

    Fixpoint eval (dt : t) (x : featureVec F.fs) : K.t :=
        match dt with
        | Leaf c => c
        | Node i t dt1 dt2 =>
            if featureTest' x i t then
                eval dt1 x
            else
                eval dt2 x
        end.

    Inductive DTSpec (x : featureVec F.fs) (c : K.t) : t -> Prop :=
    | leafPath : DTSpec x c (Leaf c)
    | nodePathLeft : forall i t dt1 dt2,
        featureTest' x i t = true -> DTSpec x c dt1 -> DTSpec x c (Node i t dt1 dt2)
    | nodePathRight : forall i t dt1 dt2,
        featureTest' x i t = false -> DTSpec x c dt2 -> DTSpec x c (Node i t dt1 dt2).

    Theorem evalCorrect : forall (dt : t) (x : featureVec F.fs) (c : K.t),
        DTSpec x c dt <-> eval dt x = c.
    Proof.
        intros; split; intro H.
        -   induction H as [
                | i t dt1 dt2 Htest IH
                | i t dt1 dt2 Htest IH ]; simpl;
                try reflexivity;
            rewrite Htest; assumption.
        -   induction dt0 as [ c' | i t dt1 IH1 dt2 IH2 ]; simpl in H;
                try (rewrite H; constructor);
            destruct (featureTest' x i t) eqn:Htest;
                [constructor 2; try assumption; auto
                |constructor 3; try assumption; auto].
    Qed.

End DTOn.

Module Type DT <: Classifier.
    Declare Module F' : FeatureSig.
    Declare Module K' : UsualDecidableType.
    Include DTOn F' K'.
End DT.