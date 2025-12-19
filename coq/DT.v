Require Import List.
Import ListNotations.

From RFXP Require Import Utils Features.

Section DecisionTrees.

    Context (class : Type) {n : nat} (fs : featureSig n).

    Inductive decisionTree : Type :=
    | Leaf (c : class)
    | Node (i : fin n)
           (t : testIndex (getFeature fs i))
           (dt1 dt2 : decisionTree).

    Inductive DTSpec
        (x : featureVec fs) (c : class) : decisionTree -> Prop :=
    | leafPath : DTSpec x c (Leaf c)
    | nodePathLeft : forall i t dt1 dt2,
        featureTest' x i t = true -> DTSpec x c dt1 -> DTSpec x c (Node i t dt1 dt2)
    | nodePathRight : forall i t dt1 dt2,
        featureTest' x i t = false -> DTSpec x c dt2 -> DTSpec x c (Node i t dt1 dt2).

    Fixpoint evalDT
        (dt : decisionTree)
        (x : featureVec fs) : class :=
        match dt with
        | Leaf c => c
        | Node i t dt1 dt2 =>
            if featureTest' x i t then
                evalDT dt1 x
            else
                evalDT dt2 x
        end.

    Theorem evalDTCorrect : forall (dt : decisionTree) (x : featureVec fs) (c : class),
        DTSpec x c dt <-> evalDT dt x = c.
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

End DecisionTrees.
