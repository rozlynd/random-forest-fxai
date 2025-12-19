open PrimFloat
open Specif
open Utils

type __ = Obj.t

type feature =
  __ -> __ -> bool
  (* singleton inductive, whose constructor was mk_feature *)

type dom = __

type testIndex = __

val boolean_feature : feature

val float_feature : feature

val enum_feature : StringSet.t -> feature

type getFeatureKind =
| Coq_isContinuousFeature
| Coq_isBooleanFeature
| Coq_isCategoricalFeature of StringSet.t

type featureSig =
| Coq_featureSigNil
| Coq_featureSigCons of int * feature * getFeatureKind * featureSig

type featureVec =
| Coq_featureVecNil
| Coq_featureVecCons of feature * getFeatureKind * dom * int * featureSig
   * featureVec

type feature_wrap = (feature, getFeatureKind) sigT

val getFeatureWrap : int -> featureSig -> fin -> feature_wrap

val getFeature : int -> featureSig -> fin -> feature

val getValueS : int -> featureSig -> featureVec -> fin -> (feature, dom) sigT

val getValue' : int -> featureSig -> featureVec -> fin -> dom

val featureTest' : int -> featureSig -> featureVec -> fin -> testIndex -> bool
