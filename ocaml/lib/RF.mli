open DT
open Enum
open Features
open List0

module StringVoting :
 sig
  val vote : string -> string list -> string

  val count_occ : string list -> string -> int
 end

type 'a nelist =
| Coq_necons of 'a * 'a list

type coq_class = string

type randomForest = coq_class decisionTree nelist

val evalRF : int -> featureList -> randomForest -> featureSpace -> coq_class
