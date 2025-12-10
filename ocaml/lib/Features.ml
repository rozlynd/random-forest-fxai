open PrimFloat
open Specif
open Utils

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type feature =
  __ -> __ -> bool
  (* singleton inductive, whose constructor was mk_feature *)

type dom = __

type testIndex = __

(** val boolean_feature : feature **)

let boolean_feature =
  Obj.magic (fun _ b -> b)

(** val float_feature : feature **)

let float_feature t0 pat =
  ltb (Obj.magic pat) (Obj.magic t0)

(** val enum_feature : StringSet.t -> feature **)

let enum_feature _ t0 x =
  Obj.magic t0 x

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

(** val getFeature : int -> featureSig -> int -> feature_wrap option **)

let rec getFeature _ fs i =
  match fs with
  | Coq_featureSigNil -> None
  | Coq_featureSigCons (wildcard', f, get, fs0) ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> Some (Coq_existT (f, get)))
       (fun i0 ->
       let filtered_var = getFeature wildcard' fs0 i0 in
       (match filtered_var with
        | Some r -> Some r
        | None -> None))
       i)

(** val getFeatureWrapSane_obligation_1 : int -> int -> feature_wrap **)

let getFeatureWrapSane_obligation_1 _ _ =
  assert false (* absurd case *)

(** val getFeatureWrapSane : int -> featureSig -> int -> feature_wrap **)

let getFeatureWrapSane n fs i =
  let filtered_var = getFeature n fs i in
  (match filtered_var with
   | Some r -> r
   | None -> getFeatureWrapSane_obligation_1 n i)

(** val getFeatureSane : int -> featureSig -> int -> feature **)

let getFeatureSane n fs i =
  projT1 (getFeatureWrapSane n fs i)

(** val getVector_obligation_3 :
    (int -> featureSig -> featureVec -> int -> (feature_wrap, dom, __) sigT2
    option) -> int -> featureSig -> featureVec -> feature -> getFeatureKind
    -> dom -> int -> featureSig -> featureVec -> int -> feature_wrap -> dom
    -> dom **)

let getVector_obligation_3 getVector0 _ _ _ _ _ _ wildcard'1 wildcard'2 vs i _ _ =
  let s = getVector0 wildcard'1 wildcard'2 vs i in
  (match s with
   | Some s0 -> let Coq_existT2 (_, d, _) = s0 in d
   | None -> assert false (* absurd case *))

(** val getVector :
    int -> featureSig -> featureVec -> int -> (feature_wrap, dom, __) sigT2
    option **)

let rec getVector n fs vs i =
  match vs with
  | Coq_featureVecNil -> None
  | Coq_featureVecCons (f, get, x, wildcard', wildcard'0, vs0) ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> Some (Coq_existT2 ((Coq_existT (f, get)), x, __)))
       (fun i0 ->
       let filtered_var = getVector wildcard' wildcard'0 vs0 i0 in
       (match filtered_var with
        | Some s ->
          let Coq_existT2 (f0, wildcard'1, _) = s in
          Some (Coq_existT2 (f0,
          (getVector_obligation_3 getVector n fs vs f get x wildcard'
            wildcard'0 vs0 i0 f0 wildcard'1), __))
        | None -> None))
       i)

(** val getVectorValueSane : int -> featureSig -> featureVec -> int -> dom **)

let getVectorValueSane n fs vs i =
  let s = getVector n fs vs i in
  (match s with
   | Some s0 -> let Coq_existT2 (_, d, _) = s0 in d
   | None -> assert false (* absurd case *))

(** val featureTest :
    int -> featureSig -> featureVec -> int -> testIndex -> bool **)

let featureTest n fs vs i t0 =
  getFeatureSane n fs i t0 (getVectorValueSane n fs vs i)
