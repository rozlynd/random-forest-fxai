open Features
open DT
open RF
open Enum
open Explainer

module InputData : Explainer.InputDataSig
with type coq_class = string = struct

  type coq_class = string

  let n_features = 4

  let features =
    Coq_featureSigCons (3, boolean_feature, Coq_isBooleanFeature,   (* blocked-arteries *)
    Coq_featureSigCons (2, boolean_feature, Coq_isBooleanFeature,   (* good-blood-circulation *)
    Coq_featureSigCons (1, boolean_feature, Coq_isBooleanFeature,   (* chest-pain *)
    Coq_featureSigCons (0, float_feature, Coq_isContinuousFeature,  (* weight *)
    Coq_featureSigNil))))

  let rec to_fin' m n =
    if n == 0 then F1 m
    else FS (m, (to_fin' m (n-1)))

  let to_fin = to_fin' n_features

  let decision_tree_1 =
    Node (to_fin 0, Obj.repr (),
      Node (to_fin 2, Obj.repr (),
        Leaf "Yes",
        Leaf "No"),
      Leaf "No")

  let decision_tree_2 =
    Node (to_fin 1, Obj.repr (),
      Leaf "No",
      Node (to_fin 3, Obj.repr 75.0,
        Leaf "No",
        Leaf "Yes"))

  let decision_tree_3 =
    Node (to_fin 1, Obj.repr (),
      Node (to_fin 0, Obj.repr (),
        Leaf "Yes",
        Leaf "No"),
      Node (to_fin 2, Obj.repr (),
        Leaf "Yes",
        Leaf "No"))

  let random_forest =
    Utils.Coq_necons (decision_tree_1, [ decision_tree_2 ; decision_tree_3 ])

  let instance =
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

end
