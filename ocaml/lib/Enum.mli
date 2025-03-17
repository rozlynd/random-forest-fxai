open Datatypes
open MSetInterface
open MSetList
open Orders
open String0

type __ = Obj.t

module StringDSO :
 DecStrOrder with type t = string

module StringOT :
 OrderedType with type t = string

module StringSet :
 Sets with module E = StringOT
