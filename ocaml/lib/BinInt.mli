open BinPos
open Datatypes

module Z :
 sig
  val compare : int -> int -> comparison

  val leb : int -> int -> bool

  val eqb : int -> int -> bool
 end
