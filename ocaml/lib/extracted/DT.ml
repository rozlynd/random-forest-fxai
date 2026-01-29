open Features
open Utils
open Xp

type 'k dt =
| Leaf of 'k
| Node of fin * testIndex * 'k dt * 'k dt

module MakeDT =
 functor (F:FeatureSig) ->
 functor (O:Output) ->
 struct
  type t = O.K.t dt

  (** val eval : t -> featureVec -> O.K.t **)

  let rec eval dt0 x =
    match dt0 with
    | Leaf c -> c
    | Node (i, t0, dt1, dt2) ->
      if featureTest' F.n F.fs x i t0 then eval dt1 x else eval dt2 x
 end
