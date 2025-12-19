open Features
open Utils

type 'class0 decisionTree =
| Leaf of 'class0
| Node of fin * testIndex * 'class0 decisionTree * 'class0 decisionTree

(** val evalDT :
    int -> featureSig -> 'a1 decisionTree -> featureVec -> 'a1 **)

let rec evalDT n fs dt x =
  match dt with
  | Leaf c -> c
  | Node (i, t, dt1, dt2) ->
    if featureTest' n fs x i t then evalDT n fs dt1 x else evalDT n fs dt2 x
