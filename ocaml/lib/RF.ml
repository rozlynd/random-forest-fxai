open DT
open Features
open List0
open Utils

module StringVoting = Voting.Voting(StringOTF)

type coq_class = string

type randomForest = coq_class decisionTree nelist

(** val evalRF :
    int -> featureSig -> randomForest -> featureVec -> coq_class **)

let evalRF n fs rf x =
  let Coq_necons (dt, dts) = rf in
  StringVoting.vote (evalDT n fs dt x)
    (map (fun dt0 -> evalDT n fs dt0 x) dts)
