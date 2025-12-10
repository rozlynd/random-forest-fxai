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

val getFeature : int -> featureSig -> int -> feature_wrap option

val getFeatureWrapSane_obligation_1 : int -> int -> feature_wrap

val getFeatureWrapSane : int -> featureSig -> int -> feature_wrap

val getFeatureSane : int -> featureSig -> int -> feature

val getVector_obligation_3 :
  (int -> featureSig -> featureVec -> int -> (feature_wrap, dom, __) sigT2
  option) -> int -> featureSig -> featureVec -> feature -> getFeatureKind ->
  dom -> int -> featureSig -> featureVec -> int -> feature_wrap -> dom -> dom

val getVector :
  int -> featureSig -> featureVec -> int -> (feature_wrap, dom, __) sigT2
  option

val getVectorValueSane : int -> featureSig -> featureVec -> int -> dom

val featureTest : int -> featureSig -> featureVec -> int -> testIndex -> bool
