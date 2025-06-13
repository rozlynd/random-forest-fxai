Require Import List.
Import ListNotations.

Require Import String.
From RFXP Require Import Utils Features DT Voting.


Module StringVoting : VotingSig StringOTF := Voting StringOTF.

Section RandomForests.

    Definition class := string.

    Context {n : nat} (fs : featureList n).

    Definition randomForest := nelist (decisionTree class fs).

    Definition evalRF (rf : randomForest) (x : featureSpace fs) : class :=
        match rf with
        | necons dt dts =>
            StringVoting.vote (evalDT class fs dt x) (map (fun dt => evalDT class fs dt x) dts)
        end.

End RandomForests.
