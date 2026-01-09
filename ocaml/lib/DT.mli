open Equalities
open Features
open Utils
open Xp

module DT :
 functor (F:FeatureSig) ->
 functor (K':UsualDecidableType) ->
 sig
  module K :
   sig
    type t = K'.t

    val eq_dec : t -> t -> bool
   end

  type t_ =
  | Leaf of K.t
  | Node of fin * testIndex * t_ * t_

  val t__rect :
    (K.t -> 'a1) -> (fin -> testIndex -> t_ -> 'a1 -> t_ -> 'a1 -> 'a1) -> t_
    -> 'a1

  val t__rec :
    (K.t -> 'a1) -> (fin -> testIndex -> t_ -> 'a1 -> t_ -> 'a1 -> 'a1) -> t_
    -> 'a1

  type t = t_

  val eval : t -> featureVec -> K.t
 end
