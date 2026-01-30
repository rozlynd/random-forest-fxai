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

module ExplanationsDefs :
 functor (E:InputProblem) ->
 sig
  type coq_Xp =
  | Coq_isAXp of E.S.t
  | Coq_isCXp of E.S.t
 end

module DummyExplainer :
 functor (E:InputProblem) ->
 sig
  module Xp :
   sig
    type coq_Xp =
    | Coq_isAXp of E.S.t
    | Coq_isCXp of E.S.t
   end

  val getNew : Xp.coq_Xp list -> Xp.coq_Xp
 end
