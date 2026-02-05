Require Import List Orders.
Import ListNotations.

Require Import String.
From RFXP Require Import Utils Features Xp DT Voting.


Module Type RFOutput <: Output.
    Declare Module K : UsualOrderedType.
End RFOutput.

Module Type RFOn (F : FeatureSig) (O : RFOutput) := TreeEnsembleOn F O.

Module Type RF := FeatureSig <+ RFOutput <+ TreeEnsembleOn.


Module MakeRF (F : FeatureSig) (O : RFOutput) <: RFOn F O.

    Module KFull : UsualOrderedTypeFull with Definition t := O.K.t := OT_to_Full O.K.
    Module KVoting : VotingSig KFull := Voting KFull.

    (* Decision trees vote for elements of K *)
    Module O_dt : Output
        with Module K := KFull.
        Module K := KFull.
    End O_dt.
    Module Dt := MakeDT F O_dt.

    Definition t := nelist Dt.t.

    Definition decide (l : nelist O_dt.K.t) :=
        match l with
        | necons x q => KVoting.vote x q
        end.

    Definition eval (rf : t) (x : featureVec F.fs) : O.K.t :=
        decide (nemap (fun dt => Dt.eval dt x) rf).

End MakeRF.