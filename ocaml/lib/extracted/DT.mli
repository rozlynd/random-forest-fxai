open Equalities
open Features
open Utils
open Xp

type 'k dt =
| Leaf of 'k
| Node of fin * testIndex * 'k dt * 'k dt

module type DT =
 sig
  val n : int

  val fs : featureSig

  module K :
   UsualDecidableType

  type t = K.t dt

  val eval : t -> featureVec -> K.t
 end

module MakeDT :
 functor (F:FeatureSig) ->
 functor (O:Output) ->
 sig
  type t = O.K.t dt

  val eval : t -> featureVec -> O.K.t
 end
