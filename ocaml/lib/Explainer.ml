open Features
open RF

module type InputDataSig =
 sig
  type coq_class = string

  val n_features : int

  val features : featureList

  val random_forest : randomForest

  val instance : featureSpace
 end

module Main =
 functor (D:InputDataSig) ->
 struct
  (** val main : unit -> D.coq_class **)

  let main _ =
    evalRF D.n_features D.features D.random_forest D.instance
 end
