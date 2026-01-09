Require Import List Equalities.
Import ListNotations.

From RFXP Require Import Utils Features Xp.

Module DT (F : FeatureSig) (K' : UsualDecidableType) <: Classifier F
    with Module K := K'.

    Module K := K'.

    Inductive _t : Type :=
    | Leaf (c : K.t)
    | Node (i : fin F.n)
           (_ : testIndex (getFeature F.fs i))
           (dt1 dt2 : _t).

    Definition t := _t.

    Inductive DTSpec (x : featureVec F.fs) (c : K.t) : t -> Prop :=
    | leafPath : DTSpec x c (Leaf c)
    | nodePathLeft : forall i t dt1 dt2,
        featureTest' x i t = true -> DTSpec x c dt1 -> DTSpec x c (Node i t dt1 dt2)
    | nodePathRight : forall i t dt1 dt2,
        featureTest' x i t = false -> DTSpec x c dt2 -> DTSpec x c (Node i t dt1 dt2).

    Fixpoint eval (dt : t) (x : featureVec F.fs) : K.t :=
        match dt with
        | Leaf c => c
        | Node i t dt1 dt2 =>
            if featureTest' x i t then
                eval dt1 x
            else
                eval dt2 x
        end.

    Theorem evalCorrect : forall (dt : t) (x : featureVec F.fs) (c : K.t),
        DTSpec x c dt <-> eval dt x = c.
    Proof.
        intros; split; intro H.
        -   induction H as [
                | i t dt1 dt2 Htest IH
                | i t dt1 dt2 Htest IH ]; simpl;
                try reflexivity;
            rewrite Htest; assumption.
        -   induction dt as [ c' | i t dt1 IH1 dt2 IH2 ]; simpl in H;
                try (rewrite H; constructor);
            destruct (featureTest' x i t) eqn:Htest;
                [constructor 2; try assumption; auto
                |constructor 3; try assumption; auto].
    Qed.

End DT.