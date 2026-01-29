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

module MakeRF :
 functor (F:FeatureSig) ->
 functor (O:RFOutput) ->
 sig
  module KFull :
   UsualOrderedTypeFull with type t = O.K.t

  module KVoting :
   sig
    val vote : O.K.t -> O.K.t list -> O.K.t

    val count_occ : O.K.t list -> O.K.t -> int
   end

  module O_dt :
   Output with module K = KFull

  module Dt :
   sig
    type t = O.K.t dt

    val eval : t -> featureVec -> O.K.t
   end

  type t = Dt.t nelist

  val eval : t -> featureVec -> O.K.t
 end
