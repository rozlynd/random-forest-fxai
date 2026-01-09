open Equalities
open Features
open Utils
open Xp

module DT =
 functor (F:FeatureSig) ->
 functor (K':UsualDecidableType) ->
 struct
  module K = K'

  type t_ =
  | Leaf of K.t
  | Node of fin * testIndex * t_ * t_

  (** val t__rect :
      (K.t -> 'a1) -> (fin -> testIndex -> t_ -> 'a1 -> t_ -> 'a1 -> 'a1) ->
      t_ -> 'a1 **)

  let rec t__rect f f0 = function
  | Leaf c -> f c
  | Node (i, t1, dt1, dt2) ->
    f0 i t1 dt1 (t__rect f f0 dt1) dt2 (t__rect f f0 dt2)

  (** val t__rec :
      (K.t -> 'a1) -> (fin -> testIndex -> t_ -> 'a1 -> t_ -> 'a1 -> 'a1) ->
      t_ -> 'a1 **)

  let rec t__rec f f0 = function
  | Leaf c -> f c
  | Node (i, t1, dt1, dt2) ->
    f0 i t1 dt1 (t__rec f f0 dt1) dt2 (t__rec f f0 dt2)

  type t = t_

  (** val eval : t -> featureVec -> K.t **)

  let rec eval dt x =
    match dt with
    | Leaf c -> c
    | Node (i, t0, dt1, dt2) ->
      if featureTest' F.n F.fs x i t0 then eval dt1 x else eval dt2 x
 end
