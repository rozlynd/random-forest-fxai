open DT
open Features
open List0
open Utils

module StringVoting :
 sig
  val vote : string -> string list -> string

  val count_occ : string list -> string -> int
 end

type coq_class = string

type randomForest = coq_class decisionTree nelist

val evalRF : int -> featureList -> randomForest -> featureSpace -> coq_class
