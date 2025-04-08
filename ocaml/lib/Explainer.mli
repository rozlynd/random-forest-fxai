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

module Main :
 functor (D:InputDataSig) ->
 sig
  val main : unit -> D.coq_class
 end
