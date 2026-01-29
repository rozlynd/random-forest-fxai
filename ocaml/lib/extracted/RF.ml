open DT
open Datatypes
open Features
open List0
open Orders
open Utils
open Xp

module type RFOutput =
 sig
  module K :
   UsualOrderedType
 end

module MakeRF =
 functor (F:FeatureSig) ->
 functor (O:RFOutput) ->
 struct
  module KFull = OT_to_Full(O.K)

  module KVoting = Voting.Voting(KFull)

  module O_dt =
   struct
    module K = KFull
   end

  module Dt = MakeDT(F)(O_dt)

  type t = Dt.t nelist

  (** val eval : t -> featureVec -> O.K.t **)

  let eval rf x =
    let Coq_necons (dt0, dts) = rf in
    KVoting.vote (Dt.eval dt0 x) (map (fun dt1 -> Dt.eval dt1 x) dts)
 end
