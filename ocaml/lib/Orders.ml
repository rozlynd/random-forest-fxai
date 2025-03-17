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

module DSO_to_OT =
 functor (O:DecStrOrder) ->
 struct
  type t = O.t

  (** val compare : t -> t -> comparison **)

  let compare =
    O.compare

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    match O.compare x y with
    | Eq -> true
    | _ -> false

  (** val eq_dec : O.t -> O.t -> bool **)

  let eq_dec x y =
    let b = match O.compare x y with
            | Eq -> true
            | _ -> false in
    if b then true else false
 end

module OT_to_Full =
 functor (O:OrderedType') ->
 struct
  type t = O.t

  (** val compare : t -> t -> comparison **)

  let compare =
    O.compare

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    O.eq_dec
 end
