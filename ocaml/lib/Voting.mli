open Datatypes
open FMapInterface
open FMapList
open List0
open PeanoNat

type __ = Obj.t

module Voting :
 functor (OTF:Orders.UsualOrderedTypeFull) ->
 sig
  val vote : OTF.t -> OTF.t list -> OTF.t

  val count_occ : OTF.t list -> OTF.t -> int
 end
