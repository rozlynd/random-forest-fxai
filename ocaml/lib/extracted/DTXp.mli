open Bool
open Equalities
open Explainers
open Features
open Utils
open Xp

type __ = Obj.t

module type DTInputProblem =
 sig
  val n : int

  val fs : featureSig

  module K :
   UsualDecidableType

  type t = K.t DT.dt

  val eval : t -> featureVec -> K.t

  val k : t

  val v : featureVec

  module S :
   FinSet
 end

module DtWCXpCheckerImpl :
 functor (C:DT.DT) ->
 functor (S:FinSet) ->
 sig
  module FD :
   sig
   end

  type coq_constraint (* AXIOM TO BE REALIZED *)

  val update : fin -> testIndex -> coq_constraint -> coq_constraint

  val nupdate : fin -> testIndex -> coq_constraint -> coq_constraint

  val witness : coq_constraint -> featureVec option

  val refute_aux :
    featureVec -> C.K.t -> S.t -> coq_constraint -> C.t -> featureVec option

  val init : S.t -> coq_constraint

  val refute : C.t -> featureVec -> S.t -> featureVec option
 end

module DtWCXpChecker :
 functor (E_:DTInputProblem) ->
 WCXpChecker with module E = E_

module DtAXpFinder :
 functor (E_:DTInputProblem) ->
 AXpFinder with module E = E_

module DtCXpFinder :
 functor (E_:DTInputProblem) ->
 CXpFinder with module E = E_
