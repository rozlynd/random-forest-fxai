open MSetInterface
open MSetList
open Orders
open OrdersEx

module StringOT :
 UsualOrderedType with type t = string

module StringSet :
 Sets with module E = StringOT

type 'a nelist =
| Coq_necons of 'a * 'a list

type fin =
| F1 of int
| FS of int * fin

val to_nat : int -> fin -> int

val to_fin : int -> int -> fin option

val to_fin' : int -> int -> fin
