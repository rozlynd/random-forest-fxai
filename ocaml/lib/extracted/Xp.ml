open Equalities
open Features
open Utils

module type FeatureSig =
 sig
  val n : int

  val fs : featureSig
 end

module type Output =
 sig
  module K :
   UsualDecidableType
 end

module type InputProblem =
 sig
  val n : int

  val fs : featureSig

  module K :
   UsualDecidableType

  type t

  val eval : t -> featureVec -> K.t

  val k : t

  val v : featureVec

  module S :
   FinSet
 end
