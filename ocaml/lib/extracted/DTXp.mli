open Bool
open Equalities
open Explainers
open Features
open FloatUtils
open PrimFloat
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

type floatRange =
| Coq_rangeUpperBound of float_std
| Coq_rangeLowerBound of float_std
| Coq_rangeBounds of float_std * float_std

type fConstraint =
| Coq_fcEmptyBool
| Coq_fcSingletonBool of bool
| Coq_fcFullBool
| Coq_fcEmptyFloat
| Coq_fcFullFloat
| Coq_fcRange of floatRange
| Coq_fcSingletonFloat of float_std
| Coq_fcSEnum of StringSet.t * (StringSet.elt -> bool)

val applyLSplit :
  feature -> testIndex -> getFeatureKind -> fConstraint -> fConstraint

val applyRSplit :
  feature -> testIndex -> getFeatureKind -> fConstraint -> fConstraint

val getWitness : feature -> getFeatureKind -> fConstraint -> dom option

type featureSpaceConstraint =
| Coq_featureSpaceConstraintNil
| Coq_featureSpaceConstraintCons of feature * getFeatureKind * fConstraint
   * int * featureSig * featureSpaceConstraint

val update :
  int -> featureSig -> featureSpaceConstraint -> fin -> (getFeatureKind ->
  fConstraint -> fConstraint) -> featureSpaceConstraint

val splitFSConstraintLeft :
  int -> featureSig -> fin -> testIndex -> featureSpaceConstraint ->
  featureSpaceConstraint

val splitFSConstraintRight :
  int -> featureSig -> fin -> testIndex -> featureSpaceConstraint ->
  featureSpaceConstraint

val witness : int -> featureSig -> featureSpaceConstraint -> featureVec option

val initConstraint :
  int -> (fin -> bool) -> featureSig -> featureVec -> featureSpaceConstraint

module DtWCXpCheckerImpl :
 functor (C:DT.DT) ->
 functor (S:FinSet) ->
 sig
  module FD :
   sig
   end

  val refute_aux :
    featureVec -> C.K.t -> S.t -> featureSpaceConstraint -> C.t -> featureVec
    option

  val init : S.t -> featureVec -> featureSpaceConstraint

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
