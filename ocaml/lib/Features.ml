open BinInt
open Enum
open PrimFloat

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

(** val testFeature :
    int -> featureList -> featureSpace -> featureIndex -> testIndex -> bool **)

let testFeature _ fs x i t0 =
  fs i t0 (x i)

(** val boolean_feature : feature **)

let boolean_feature _ b =
  Obj.magic b

type int_test =
| Coq_int_eq
| Coq_int_le

(** val int_feature : feature **)

let int_feature pat a =
  let (t0, b) = Obj.magic pat in
  (match t0 with
   | Coq_int_eq -> Z.eqb (Obj.magic a) b
   | Coq_int_le -> Z.leb (Obj.magic a) b)

(** val float_feature : feature **)

let float_feature y x =
  ltb (Obj.magic x) (Obj.magic y)

(** val enum_feature : StringSet.t -> feature **)

let enum_feature _ p x =
  Obj.magic p x
