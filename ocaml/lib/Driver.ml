open Extracted

open Utils
open Features
open Xp
open Explainers
open DT
open DTXp

module F : FeatureSig = struct

  let n = 4

  let fs =
    Coq_featureSigCons (3, boolean_feature, Coq_isBooleanFeature,   (* blocked-arteries *)
    Coq_featureSigCons (2, boolean_feature, Coq_isBooleanFeature,   (* good-blood-circulation *)
    Coq_featureSigCons (1, boolean_feature, Coq_isBooleanFeature,   (* chest-pain *)
    Coq_featureSigCons (0, float_feature, Coq_isContinuousFeature,  (* weight *)
    Coq_featureSigNil))))

end

module O : Output
  with module K = StringOT
    = struct

  module K = StringOT

end

module Dt = MakeDT (F) (O)

module Input : DTInputProblem = struct

  let n = F.n

  let fs = F.fs

  module K = O.K

  type t = Dt.t

  let eval = Dt.eval

  let to_fin = to_fin' F.n

  let k =
    Node (to_fin 1, Obj.repr (),
      Node (to_fin 0, Obj.repr (),
        Leaf "Yes",
        Leaf "No"),
      Node (to_fin 2, Obj.repr (),
        Leaf "Yes",
        Leaf "No"))

  let v =
    Coq_featureVecCons (boolean_feature, Coq_isBooleanFeature, Obj.repr true, 3,
      (Coq_featureSigCons (2, boolean_feature, Coq_isBooleanFeature,
      (Coq_featureSigCons (1, boolean_feature, Coq_isBooleanFeature,
      (Coq_featureSigCons (0, float_feature, Coq_isContinuousFeature,
      Coq_featureSigNil)))))),
    Coq_featureVecCons (boolean_feature, Coq_isBooleanFeature, Obj.repr false, 2,
      (Coq_featureSigCons (1, boolean_feature, Coq_isBooleanFeature,
      (Coq_featureSigCons (0, float_feature, Coq_isContinuousFeature,
      Coq_featureSigNil)))),
    Coq_featureVecCons (boolean_feature, Coq_isBooleanFeature, Obj.repr true, 1,
      (Coq_featureSigCons (0, float_feature, Coq_isContinuousFeature,
      Coq_featureSigNil)),
    Coq_featureVecCons (float_feature, Coq_isContinuousFeature, Obj.repr 70.0, 0,
      Coq_featureSigNil,
    Coq_featureVecNil))))

  module S = MakeFinSet (struct let n = n end)

end

module Find = DtAXpFinder (Input)
