open Bool
open Datatypes
open Equalities
open Explainers
open Features
open FloatUtils
open PrimFloat
open Utils
open Xp

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

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

type boolConstraint =
| BEmpty
| BTrue
| BFalse
| BAny

type floatConstraint =
| FEmpty
| FSingleton of float_std
| FRange of float_std * float_std

type senumConstraint =
  StringSet.t
  (* singleton inductive, whose constructor was SEnum *)

(** val boolConstraintWitness : boolConstraint -> bool option **)

let boolConstraintWitness = function
| BEmpty -> None
| BFalse -> Some false
| _ -> Some true

(** val floatConstraintWitness : floatConstraint -> float_std option **)

let floatConstraintWitness = function
| FEmpty -> None
| FSingleton a -> Some a
| FRange (a, b) ->
  if is_infinity a
  then if is_infinity b
       then Some (Float64.of_float (0x0p+0))
       else Some (next_down b)
  else Some a

(** val senumConstraintWitness :
    StringSet.t -> senumConstraint -> string_enum option **)

let senumConstraintWitness _ c =
  let filtered_var = StringSet.choose c in
  (match filtered_var with
   | Some x -> Some x
   | None -> None)

(** val boolConstraintLeftSplit : boolConstraint -> boolConstraint **)

let boolConstraintLeftSplit = function
| BEmpty -> BEmpty
| BFalse -> BEmpty
| _ -> BTrue

(** val boolConstraintRightSplit : boolConstraint -> boolConstraint **)

let boolConstraintRightSplit = function
| BEmpty -> BEmpty
| BTrue -> BEmpty
| _ -> BFalse

(** val floatConstraintLeftSplit :
    float_test -> floatConstraint -> floatConstraint **)

let floatConstraintLeftSplit t0 c =
  if is_infinity t0
  then if get_sign t0 then c else FEmpty
  else (match c with
        | FEmpty -> FEmpty
        | FSingleton a -> if ltb a t0 then FSingleton a else FEmpty
        | FRange (a, b) ->
          if ltb a t0
          then if ltb b t0 then FRange (a, b) else FRange (a, t0)
          else FEmpty)

(** val floatConstraintRightSplit :
    float_test -> floatConstraint -> floatConstraint **)

let floatConstraintRightSplit t0 c =
  if is_infinity t0
  then if get_sign t0 then FEmpty else c
  else (match c with
        | FEmpty -> FEmpty
        | FSingleton a -> if ltb a t0 then FEmpty else FSingleton a
        | FRange (a, b) ->
          if ltb b t0
          then FEmpty
          else if ltb a t0 then FRange (t0, b) else FRange (a, b))

(** val senumConstraintLeftSplit :
    StringSet.t -> string_enum_test -> senumConstraint -> senumConstraint **)

let senumConstraintLeftSplit _ =
  StringSet.filter

(** val senumConstraintRightSplit :
    StringSet.t -> string_enum_test -> senumConstraint -> senumConstraint **)

let senumConstraintRightSplit _ t0 c =
  StringSet.filter (fun x -> negb (t0 x)) c

(** val boolConstraintInitFull : boolConstraint **)

let boolConstraintInitFull =
  BAny

(** val floatConstraintInitFull : floatConstraint **)

let floatConstraintInitFull =
  FRange (neg_infinity, infinity)

(** val senumConstraintInitFull : StringSet.t -> senumConstraint **)

let senumConstraintInitFull s =
  s

(** val boolConstraintInitSingleton : bool -> boolConstraint **)

let boolConstraintInitSingleton = function
| true -> BTrue
| false -> BFalse

(** val floatConstraintInitSingleton : float_std -> floatConstraint **)

let floatConstraintInitSingleton x =
  FSingleton x

(** val senumConstraintInitSingleton :
    StringSet.t -> string_enum -> senumConstraint **)

let senumConstraintInitSingleton _ =
  StringSet.singleton

type fConstraint =
| CBool of boolConstraint
| CFloat of floatConstraint
| CSEnum of StringSet.t * senumConstraint

(** val constraintWitness :
    feature -> getFeatureKind -> fConstraint -> dom option **)

let constraintWitness _ get c =
  match get with
  | Coq_isContinuousFeature ->
    (match c with
     | CFloat c0 ->
       let c1 = Obj.magic c0 in Obj.magic floatConstraintWitness c1
     | _ -> assert false (* absurd case *))
  | Coq_isBooleanFeature ->
    (match c with
     | CBool c0 -> let c1 = Obj.magic c0 in Obj.magic boolConstraintWitness c1
     | _ -> assert false (* absurd case *))
  | Coq_isStringEnumFeature s ->
    (match c with
     | CSEnum (_, c0) ->
       let c1 = Obj.magic c0 in
       let s0 = Obj.magic s in Obj.magic senumConstraintWitness s0 c1
     | _ -> assert false (* absurd case *))

(** val constraintLeftSplit :
    feature -> getFeatureKind -> testIndex -> fConstraint -> fConstraint **)

let constraintLeftSplit _ = function
| Coq_isContinuousFeature ->
  Obj.magic (fun t0 c ->
    match c with
    | CFloat c0 -> CFloat (floatConstraintLeftSplit t0 c0)
    | _ -> assert false (* absurd case *))
| Coq_isBooleanFeature ->
  Obj.magic (fun _ c ->
    match c with
    | CBool c0 -> CBool (boolConstraintLeftSplit c0)
    | _ -> assert false (* absurd case *))
| Coq_isStringEnumFeature s ->
  let s0 = Obj.magic s in
  Obj.magic (fun t0 c ->
    match c with
    | CSEnum (_, c0) -> CSEnum (s0, (senumConstraintLeftSplit s0 t0 c0))
    | _ -> assert false (* absurd case *))

(** val constraintRightSplit :
    feature -> getFeatureKind -> testIndex -> fConstraint -> fConstraint **)

let constraintRightSplit _ = function
| Coq_isContinuousFeature ->
  Obj.magic (fun t0 c ->
    match c with
    | CFloat c0 -> CFloat (floatConstraintRightSplit t0 c0)
    | _ -> assert false (* absurd case *))
| Coq_isBooleanFeature ->
  Obj.magic (fun _ c ->
    match c with
    | CBool c0 -> CBool (boolConstraintRightSplit c0)
    | _ -> assert false (* absurd case *))
| Coq_isStringEnumFeature s ->
  let s0 = Obj.magic s in
  Obj.magic (fun t0 c ->
    match c with
    | CSEnum (_, c0) -> CSEnum (s0, (senumConstraintRightSplit s0 t0 c0))
    | _ -> assert false (* absurd case *))

(** val constraintInitFull : feature -> getFeatureKind -> fConstraint **)

let constraintInitFull _ = function
| Coq_isContinuousFeature -> CFloat floatConstraintInitFull
| Coq_isBooleanFeature -> CBool boolConstraintInitFull
| Coq_isStringEnumFeature s -> CSEnum (s, (senumConstraintInitFull s))

(** val constraintInitSingleton :
    feature -> getFeatureKind -> dom -> fConstraint **)

let constraintInitSingleton _ get x =
  match get with
  | Coq_isContinuousFeature ->
    CFloat (floatConstraintInitSingleton (Obj.magic x))
  | Coq_isBooleanFeature -> CBool (boolConstraintInitSingleton (Obj.magic x))
  | Coq_isStringEnumFeature s ->
    CSEnum (s, (senumConstraintInitSingleton s (Obj.magic x)))

type featureSpaceConstraint =
| Coq_featureSpaceConstraintNil
| Coq_featureSpaceConstraintCons of feature * getFeatureKind * fConstraint
   * int * featureSig * featureSpaceConstraint

(** val update :
    int -> featureSig -> featureSpaceConstraint -> fin -> (getFeatureKind ->
    fConstraint -> fConstraint) -> featureSpaceConstraint **)

let rec update _ _ cs i =
  match cs with
  | Coq_featureSpaceConstraintNil -> (fun _ -> Coq_featureSpaceConstraintNil)
  | Coq_featureSpaceConstraintCons (f, get, c, n0, fs0, cs0) ->
    let x = update n0 fs0 cs0 in
    (fun ap ->
    match i with
    | F1 n1 ->
      Coq_featureSpaceConstraintCons (f, get, (ap get c), n1, fs0, cs0)
    | FS (n1, i0) ->
      Coq_featureSpaceConstraintCons (f, get, c, n1, fs0, (x i0 ap)))

(** val splitFSConstraintLeft :
    int -> featureSig -> fin -> testIndex -> featureSpaceConstraint ->
    featureSpaceConstraint **)

let splitFSConstraintLeft n0 fs0 i t0 cs =
  update n0 fs0 cs i (fun get ->
    constraintLeftSplit (getFeature n0 fs0 i) get t0)

(** val splitFSConstraintRight :
    int -> featureSig -> fin -> testIndex -> featureSpaceConstraint ->
    featureSpaceConstraint **)

let splitFSConstraintRight n0 fs0 i t0 cs =
  update n0 fs0 cs i (fun get ->
    constraintRightSplit (getFeature n0 fs0 i) get t0)

(** val witness :
    int -> featureSig -> featureSpaceConstraint -> featureVec option **)

let rec witness _ _ = function
| Coq_featureSpaceConstraintNil -> Some Coq_featureVecNil
| Coq_featureSpaceConstraintCons (f, get, c, n0, fs0, cs0) ->
  (match constraintWitness f get c with
   | Some x ->
     (match witness n0 fs0 cs0 with
      | Some vs -> Some (Coq_featureVecCons (f, get, x, n0, fs0, vs))
      | None -> None)
   | None -> None)

(** val initConstraint :
    int -> (fin -> bool) -> featureSig -> featureVec -> featureSpaceConstraint **)

let rec initConstraint _ x _ = function
| Coq_featureVecNil -> Coq_featureSpaceConstraintNil
| Coq_featureVecCons (f, get, x0, n0, fs0, vs0) ->
  let c =
    if x (F1 n0)
    then constraintInitFull f get
    else constraintInitSingleton f get x0
  in
  Coq_featureSpaceConstraintCons (f, get, c, n0, fs0,
  (initConstraint n0 (fun k0 -> x (FS (n0, k0))) fs0 vs0))

module DtWCXpCheckerImpl =
 functor (C:DT.DT) ->
 functor (S:FinSet) ->
 struct
  module FD = FeatureSigDefs(C)(S)

  (** val refute_aux :
      featureVec -> C.K.t -> S.t -> featureSpaceConstraint -> C.t ->
      featureVec option **)

  let rec refute_aux v0 c0 x c = function
  | DT.Leaf c1 -> if C.K.eq_dec c1 c0 then None else witness C.n C.fs c
  | DT.Node (i, test, dt1, dt2) ->
    if S.mem i x
    then (match refute_aux v0 c0 x (splitFSConstraintLeft C.n C.fs i test c)
                  dt1 with
          | Some r -> Some r
          | None ->
            refute_aux v0 c0 x (splitFSConstraintRight C.n C.fs i test c) dt2)
    else let dt' = if featureTest' C.n C.fs v0 i test then dt1 else dt2 in
         refute_aux v0 c0 x c dt'

  (** val init : S.t -> featureVec -> featureSpaceConstraint **)

  let init x =
    initConstraint S.n (fun i -> S.mem i x) C.fs

  (** val refute : C.t -> featureVec -> S.t -> featureVec option **)

  let refute dt0 v0 x =
    refute_aux v0 (C.eval dt0 v0) x (init x v0) dt0
 end

module DtWCXpChecker =
 functor (E_:DTInputProblem) ->
 struct
  module E = E_

  module Xp = ExplainersDefs(E)

  module Impl = DtWCXpCheckerImpl(E)(E.S)

  (** val checkWCXp : E_.S.t -> bool **)

  let checkWCXp x =
    match Impl.refute E.k E.v x with
    | Some _ -> true
    | None -> false

  (** val checkWCXpSound : E.S.t -> reflect **)

  let checkWCXpSound x =
    let o = Impl.refute E.k E.v x in
    (match o with
     | Some _ -> ReflectT
     | None -> ReflectF)
 end

module DtAXpFinder =
 functor (E_:DTInputProblem) ->
 struct
  module Chk = DtWCXpChecker(E_)

  module Impl = AXpIterativeFinder(E_)(Chk)

  module E = E_

  module Xp = Impl.Xp

  (** val findAXp : E.S.t -> E.S.t **)

  let findAXp =
    Impl.findAXp

  (** val findAXpSound : __ **)

  let findAXpSound =
    __

  (** val findAXpSane : __ **)

  let findAXpSane =
    __
 end

module DtCXpFinder =
 functor (E_:DTInputProblem) ->
 struct
  module Chk = DtWCXpChecker(E_)

  module Impl = CXpIterativeFinder(E_)(Chk)

  module E = E_

  module Xp = Impl.Xp

  (** val findCXp : E.S.t -> E.S.t **)

  let findCXp =
    Impl.findCXp

  (** val findCXpSound : __ **)

  let findCXpSound =
    __

  (** val findCXpSane : __ **)

  let findCXpSane =
    __
 end
