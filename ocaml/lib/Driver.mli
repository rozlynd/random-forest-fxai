open Extracted

open Utils
open DT
open Features

module RF : sig

  module Dt : sig
    type t = string dt
    val eval : t -> featureVec -> string
  end

  type t = Dt.t nelist
  val eval : t -> featureVec -> string

end

val random_forest : RF.t

val instance : featureVec
