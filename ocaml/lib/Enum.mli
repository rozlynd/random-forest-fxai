open MSetInterface
open MSetList
open Orders
open OrdersEx

module StringOT :
 OrderedType with type t = string

module StringSet :
 Sets with module E = StringOT
