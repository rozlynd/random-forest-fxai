open MSetInterface
open MSetList
open Orders
open OrdersEx

module StringOT :
 UsualOrderedType with type t = string

module StringOTF :
 UsualOrderedTypeFull with type t = string

module StringSet :
 Sets with module E = StringOT

type 'a nelist =
| Coq_necons of 'a * 'a list
