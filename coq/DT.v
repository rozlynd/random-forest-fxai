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


Module Type DTOn (F : FeatureSig) (O : Output) := ClassifierOn F O
    with Definition t := dt F.fs O.K.t.

Module Type DT <: Classifier := FeatureSig <+ Output <+ DTOn.


Module MakeDT (F : FeatureSig) (O : Output) <: DTOn F O.
    
    Definition t := dt F.fs O.K.t.

    Fixpoint eval (dt : t) (x : featureVec F.fs) : O.K.t :=
        match dt with
        | Leaf c => c
        | Node i t dt1 dt2 =>
            if featureTest' x i t then
                eval dt1 x
            else
                eval dt2 x
        end.

    Inductive DTSpec (x : featureVec F.fs) (c : O.K.t) : t -> Prop :=
    | leafPath : DTSpec x c (Leaf c)
    | nodePathLeft : forall i t dt1 dt2,
        featureTest' x i t = true -> DTSpec x c dt1 -> DTSpec x c (Node i t dt1 dt2)
    | nodePathRight : forall i t dt1 dt2,
        featureTest' x i t = false -> DTSpec x c dt2 -> DTSpec x c (Node i t dt1 dt2).

    Theorem evalCorrect : forall (dt : t) (x : featureVec F.fs) (c : O.K.t),
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

End MakeDT.


Module Type TreeEnsembleOn (F : FeatureSig) (O : Output) <: ClassifierOn F O.

    Declare Module O_dt : Output.
    Declare Module Dt : DTOn F O_dt.
    
    Parameter decide : nelist O_dt.K.t -> O.K.t.

    Include ClassifierOn F O
        with Definition t := nelist Dt.t
        with Definition eval := fun dts v => decide (nemap (fun dt => Dt.eval dt v) dts).

End TreeEnsembleOn.

Module Type TreeEnsemble := FeatureSig <+ Output <+ TreeEnsembleOn.