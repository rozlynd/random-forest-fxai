open Datatypes

module type DecStrOrder =
 sig
  type t

  val compare : t -> t -> comparison
 end

module type OrderedType =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module type OrderedType' =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module DSO_to_OT :
 functor (O:DecStrOrder) ->
 sig
  type t = O.t

  val compare : t -> t -> comparison

  val eqb : O.t -> O.t -> bool

  val eq_dec : O.t -> O.t -> bool
 end

module OT_to_Full :
 functor (O:OrderedType') ->
 sig
  type t = O.t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end
