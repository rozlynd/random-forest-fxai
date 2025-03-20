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

let boolean_feature =
  Obj.magic (fun _ b -> b)

type int_test =
| Coq_int_eq of Z.t
| Coq_int_le of Z.t

(** val int_feature : feature **)

let int_feature t0 a =
  match Obj.magic t0 with
  | Coq_int_eq b -> Z.eqb (Obj.magic a) b
  | Coq_int_le b -> Z.leb (Obj.magic a) b

(** val float_feature : feature **)

let float_feature t0 x =
  ltb (Obj.magic x) (Obj.magic t0)

(** val enum_feature : StringSet.t -> feature **)

let enum_feature _ t0 x =
  Obj.magic t0 x
