open DT
open Features

module type InputDataSig =
 sig
  type coq_class

  val n_features : int

  val features : featureList

  val decision_tree : coq_class decisionTree

  val instance : featureSpace
 end

module Main =
 functor (D:InputDataSig) ->
 struct
  (** val main : unit -> D.coq_class **)

  let main _ =
    evalDT D.n_features D.features D.decision_tree D.instance
 end
