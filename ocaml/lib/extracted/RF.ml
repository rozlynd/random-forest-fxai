open DT
open Datatypes
open Features
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

  (** val decide : O_dt.K.t nelist -> O.K.t **)

  let decide = function
  | Coq_necons (x, q) -> KVoting.vote x q

  (** val eval : t -> featureVec -> O.K.t **)

  let eval rf x =
    decide (nemap (fun dt0 -> Dt.eval dt0 x) rf)
 end
