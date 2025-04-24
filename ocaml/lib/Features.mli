open BinInt
open PrimFloat
open Utils

type __ = Obj.t

type ('x, 'a) indexed = 'x -> 'a

type 'a predicate = 'a -> bool

type feature =
  (__, __ predicate) indexed
  (* singleton inductive, whose constructor was mk_feature *)

type dom = __

type testIndex = __

type featureIndex = int

type featureList = (featureIndex, feature) indexed

type featureSpace = (featureIndex, dom) indexed

val testFeature :
  int -> featureList -> featureSpace -> featureIndex -> testIndex -> bool

val boolean_feature : feature

type int_test =
| Coq_int_eq of Z.t
| Coq_int_le of Z.t

val int_feature : feature

val float_feature : feature

val enum_feature : StringSet.t -> feature
