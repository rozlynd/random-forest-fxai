open BinPos
open Datatypes

module Z :
 sig
  type t = int

  val compare : int -> int -> comparison

  val leb : int -> int -> bool

  val eqb : int -> int -> bool
 end
