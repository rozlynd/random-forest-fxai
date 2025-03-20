open Features
open DT
open Enum
open Explainer

module InputData : Explainer.InputDataSig
with type coq_class = string = struct

  (* A silly example of a DT deciding if you can get a loan; tests every kind of feature *)

  type coq_class = string

  let s : StringSet.t =
    List.fold_right (fun x s -> StringSet.add x s)
    [ "blue" ; "red" ; "green" ]
    StringSet.empty

  let n_features = 4

  let features = (fun n -> begin
    if n = 0 then
      int_feature
    else if n = 1 then
      float_feature
    else if n = 2 then
      boolean_feature
    else if n = 3 then
      enum_feature s
    else
      failwith "error"
  end)

  let decision_tree =
    Node (2, Obj.repr (),
      Node (0, Obj.repr (Coq_int_le 24),
        Leaf "No loan (age must be >= 25)",
        Node (1, Obj.repr 100000.0,
          Leaf "No loan (salary must be > 100 000)",
          Node (3, Obj.repr (fun x -> List.mem x [ "blue" ; "red" ]),
            Leaf "You get a loan!",
            Leaf "No loan (favorite color must be blue or red)"))),
      Leaf "No loan (must be married)")

  let instance = (fun n -> List.nth [
    Obj.repr 30 ;
    Obj.repr 200000.0 ;
    Obj.repr true ;
    Obj.repr "blue"
  ] n)

end
