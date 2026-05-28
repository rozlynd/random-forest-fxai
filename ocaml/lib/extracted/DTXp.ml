open Bool
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

(** val applyLSplit :
    feature -> testIndex -> getFeatureKind -> fConstraint -> fConstraint **)

let applyLSplit _ t0 = function
| Coq_isContinuousFeature ->
  (fun c ->
    match c with
    | Coq_fcSingletonBool x -> Obj.magic __ x t0
    | Coq_fcEmptyFloat -> Coq_fcEmptyFloat
    | Coq_fcFullFloat -> Coq_fcRange (Coq_rangeUpperBound (Obj.magic t0))
    | Coq_fcRange r ->
      (match r with
       | Coq_rangeUpperBound b ->
         let x = Obj.magic t0 in
         if ltb x b
         then Coq_fcRange (Coq_rangeUpperBound x)
         else Coq_fcRange (Coq_rangeUpperBound b)
       | Coq_rangeLowerBound a ->
         if ltb a (Obj.magic t0) then Coq_fcEmptyFloat else Coq_fcFullFloat
       | Coq_rangeBounds (_, _) -> Coq_fcFullFloat)
    | Coq_fcSingletonFloat y ->
      if ltb y (Obj.magic t0)
      then Coq_fcSingletonFloat y
      else Coq_fcEmptyFloat
    | Coq_fcSEnum (x, x0) -> Obj.magic __ x x0 t0
    | _ -> Obj.magic __ t0)
| Coq_isBooleanFeature -> Obj.magic (fun c -> c)
| Coq_isStringEnumFeature _ -> (fun c -> c)

(** val applyRSplit :
    feature -> testIndex -> getFeatureKind -> fConstraint -> fConstraint **)

let applyRSplit _ _ _ c =
  c

(** val getWitness :
    feature -> getFeatureKind -> fConstraint -> dom option **)

let getWitness _ get c =
  match get with
  | Coq_isContinuousFeature ->
    (match c with
     | Coq_fcEmptyFloat -> None
     | Coq_fcFullFloat -> Obj.magic (Some (Float64.of_float (0x0p+0)))
     | Coq_fcRange r ->
       (match r with
        | Coq_rangeUpperBound a ->
          let a0 = Obj.magic a in
          Obj.magic (Some (sub a0 (Float64.of_float (0x1p+0))))
        | Coq_rangeLowerBound a ->
          let a0 = Obj.magic a in
          Obj.magic (Some (add a0 (Float64.of_float (0x1p+0))))
        | Coq_rangeBounds (a, b) ->
          let a0 = Obj.magic a in
          let b0 = Obj.magic b in
          Obj.magic (Some (div (add a0 b0) (Float64.of_float (0x1p+1)))))
     | Coq_fcSingletonFloat x -> let x0 = Obj.magic x in Obj.magic (Some x0)
     | Coq_fcSEnum (_, _) -> assert false (* absurd case *)
     | _ -> assert false (* absurd case *))
  | Coq_isBooleanFeature ->
    (match c with
     | Coq_fcEmptyBool -> None
     | Coq_fcSingletonBool b -> let b0 = Obj.magic b in Obj.magic (Some b0)
     | Coq_fcFullBool -> Obj.magic (Some true)
     | Coq_fcSEnum (_, _) -> assert false (* absurd case *)
     | _ -> assert false (* absurd case *))
  | Coq_isStringEnumFeature _ ->
    (match c with
     | Coq_fcEmptyBool -> assert false (* absurd case *)
     | Coq_fcSingletonBool _ -> assert false (* absurd case *)
     | Coq_fcFullBool -> assert false (* absurd case *)
     | Coq_fcSEnum (s, p) ->
       let s0 = Obj.magic s in
       let p0 = Obj.magic p in
       let filtered_var = StringSet.choose (StringSet.filter p0 s0) in
       (match filtered_var with
        | Some e -> Obj.magic (Some e)
        | None -> Obj.magic None)
     | _ -> assert false (* absurd case *))

type featureSpaceConstraint =
| Coq_featureSpaceConstraintNil
| Coq_featureSpaceConstraintCons of feature * getFeatureKind * fConstraint
   * int * featureSig * featureSpaceConstraint

(** val mapOne :
    int -> featureSig -> featureSpaceConstraint -> fin -> (getFeatureKind ->
    fConstraint -> fConstraint) -> featureSpaceConstraint **)

let rec mapOne _ _ cs i =
  match cs with
  | Coq_featureSpaceConstraintNil -> (fun _ -> Coq_featureSpaceConstraintNil)
  | Coq_featureSpaceConstraintCons (f, get, c, n0, fs0, cs0) ->
    let x = mapOne n0 fs0 cs0 in
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
  mapOne n0 fs0 cs i (applyLSplit (getFeature n0 fs0 i) t0)

(** val splitFSConstraintRight :
    int -> featureSig -> fin -> testIndex -> featureSpaceConstraint ->
    featureSpaceConstraint **)

let splitFSConstraintRight n0 fs0 i t0 cs =
  mapOne n0 fs0 cs i (applyRSplit (getFeature n0 fs0 i) t0)

(** val witness :
    int -> featureSig -> featureSpaceConstraint -> featureVec option **)

let rec witness _ _ = function
| Coq_featureSpaceConstraintNil -> Some Coq_featureVecNil
| Coq_featureSpaceConstraintCons (f, get, c, n0, fs0, cs0) ->
  (match getWitness f get c with
   | Some x ->
     (match witness n0 fs0 cs0 with
      | Some vs -> Some (Coq_featureVecCons (f, get, x, n0, fs0, vs))
      | None -> None)
   | None -> None)

(** val initConstraint :
    int -> (fin -> bool) -> featureSig -> featureVec -> featureSpaceConstraint **)

let rec initConstraint _ x _ = function
| Coq_featureVecNil -> Coq_featureSpaceConstraintNil
| Coq_featureVecCons (f, get, _, n0, fs0, vs0) ->
  let c =
    match get with
    | Coq_isContinuousFeature -> Coq_fcFullFloat
    | Coq_isBooleanFeature -> Coq_fcFullBool
    | Coq_isStringEnumFeature s -> Coq_fcSEnum (s, (fun _ -> true))
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
