open DTXp
open Equalities
open Features

module type DTInstance =
 sig
  val n : int

  val fs : featureSig

  module K :
   UsualDecidableType

  type t = K.t DT.dt

  val eval : t -> featureVec -> K.t

  val k : t
 end

val initConstraintFull : int -> featureSig -> featureSpaceConstraint

module DtGenVectors :
 functor (Dt:DTInstance) ->
 sig
  val gen_aux :
    featureSpaceConstraint -> Dt.t -> featureVec list -> featureVec list

  val gen : unit -> featureVec list
 end
