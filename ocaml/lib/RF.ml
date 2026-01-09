open Datatypes
open Features
open List0
open Orders
open Utils
open Xp

module RF =
 functor (F:FeatureSig) ->
 functor (K':UsualOrderedType) ->
 struct
  module K = K'

  module KFull = OT_to_Full(K')

  module KVoting = Voting.Voting(KFull)

  module Dt = DT.DT(F)(K)

  type t = Dt.t nelist

  (** val eval : t -> featureVec -> K.t **)

  let eval rf x =
    let Coq_necons (dt, dts) = rf in
    KVoting.vote (Dt.eval dt x) (map (fun dt0 -> Dt.eval dt0 x) dts)
 end
