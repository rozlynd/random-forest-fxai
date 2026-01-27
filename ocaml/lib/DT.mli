open Features
open Utils
open Xp

type 'k dt =
| Leaf of 'k
| Node of fin * testIndex * 'k dt * 'k dt

module MakeDT :
 functor (F:FeatureSig) ->
 functor (O:Output) ->
 sig
  type t = O.K.t dt

  val eval : t -> featureVec -> O.K.t
 end
