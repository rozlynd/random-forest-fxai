open DT
open Enum
open Features
open List0
open Orders

module StringVoting :
 sig
  module OTF :
   UsualOrderedTypeFull with type t = string

  val vote : OTF.t -> OTF.t list -> OTF.t

  val count_occ : OTF.t list -> OTF.t -> int
 end

type 'a nelist =
| Coq_necons of 'a * 'a list

type coq_class = string

type randomForest = coq_class decisionTree nelist

val evalRF : int -> featureList -> randomForest -> featureSpace -> coq_class
