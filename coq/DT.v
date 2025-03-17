Require Import List.
Import ListNotations.

From RFXP Require Import Features.

Section DecisionTrees.

    Context (class : Set) {n : nat} (fs : featureList n).

    Inductive decisionTree : Type :=
    | Leaf (c : class)
    | Node (i : featureIndex n)
           (t : testIndex (fs i))
           (dt1 dt2 : decisionTree).

    Fixpoint evalDT
        (dt : decisionTree)
        (x : featureSpace fs) : class :=
        match dt with
        | Leaf c => c
        | Node i t dt1 dt2 =>
            if testFeature x i t then
                evalDT dt1 x
            else
                evalDT dt2 x
        end.

End DecisionTrees.
