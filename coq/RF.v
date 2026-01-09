Require Import List Orders.
Import ListNotations.

Require Import String.
From RFXP Require Import Utils Features Xp DT Voting.


Module RF (F : FeatureSig) (K' : UsualOrderedType) <: Classifier F
    with Module K := K'.

    Module K := K'.
    Module KFull : UsualOrderedTypeFull with Definition t := K.t := OT_to_Full K'.
    Module KVoting : VotingSig KFull := Voting KFull.

    Module Dt := DT F K.

    Definition t := nelist Dt.t.

    Definition eval (rf : t) (x : featureVec F.fs) : K.t :=
        match rf with
        | necons dt dts =>
            KVoting.vote (Dt.eval dt x) (map (fun dt => Dt.eval dt x) dts)
        end.

End RF.