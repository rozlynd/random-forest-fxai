open Features
open DT
open RF
open Enum
open Explainer

module InputData : Explainer.InputDataSig
with type coq_class = string = struct

  type coq_class = string

  let n_features = 4

  let features = (fun n -> begin
    if n = 0 then
      boolean_feature (* blocked-arteries *)
    else if n = 1 then
      boolean_feature (* good-blood-circulation *)
    else if n = 2 then
      boolean_feature (* chest-pain *)
    else if n = 3 then
      float_feature (* weight *)
    else
      failwith "error"
  end)

  let decision_tree_1 =
    Node (0, Obj.repr (),
      Node (2, Obj.repr (),
        Leaf "Yes",
        Leaf "No"),
      Leaf "No")

  let decision_tree_2 =
    Node (1, Obj.repr (),
      Leaf "No",
      Node (3, Obj.repr 75.0,
        Leaf "No",
        Leaf "Yes"))

  let decision_tree_3 =
    Node (1, Obj.repr (),
      Node (0, Obj.repr (),
        Leaf "Yes",
        Leaf "No"),
      Node (2, Obj.repr (),
        Leaf "Yes",
        Leaf "No"))

  let random_forest =
    Coq_necons (decision_tree_1, [ decision_tree_2 ; decision_tree_3 ])

  let instance = (fun n -> List.nth [
    Obj.repr true ;
    Obj.repr false ;
    Obj.repr true ;
    Obj.repr 70.0
  ] n)

end
