open MSetInterface
open MSetList
open Orders
open OrdersEx

module StringOT = String_as_OT

module StringOTF = OT_to_Full(StringOT)

module StringSet = Make(StringOT)

type 'a nelist =
| Coq_necons of 'a * 'a list
