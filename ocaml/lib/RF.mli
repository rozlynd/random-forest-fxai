open Datatypes
open Features
open List0
open Orders
open Utils
open Xp

module RF :
 functor (F:FeatureSig) ->
 functor (K':UsualOrderedType) ->
 sig
  module K :
   sig
    type t = K'.t

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> bool
   end

  module KFull :
   UsualOrderedTypeFull with type t = K.t

  module KVoting :
   sig
    val vote : K.t -> K.t list -> K.t

    val count_occ : K.t list -> K.t -> int
   end

  module Dt :
   sig
    module K :
     sig
      type t = K'.t

      val eq_dec : K'.t -> K'.t -> bool
     end

    type t_ =
    | Leaf of K'.t
    | Node of fin * testIndex * t_ * t_

    val t__rect :
      (K'.t -> 'a1) -> (fin -> testIndex -> t_ -> 'a1 -> t_ -> 'a1 -> 'a1) ->
      t_ -> 'a1

    val t__rec :
      (K'.t -> 'a1) -> (fin -> testIndex -> t_ -> 'a1 -> t_ -> 'a1 -> 'a1) ->
      t_ -> 'a1

    type t = t_

    val eval : t -> featureVec -> K'.t
   end

  type t = Dt.t nelist

  val eval : t -> featureVec -> K.t
 end
