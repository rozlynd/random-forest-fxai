open OrdersTac

type 'x coq_Compare =
| LT
| EQ
| GT

module type MiniOrderedType =
 sig
  type t

  val compare : t -> t -> t coq_Compare
 end

module type OrderedType =
 sig
  type t

  val compare : t -> t -> t coq_Compare

  val eq_dec : t -> t -> bool
 end

module MOT_to_OT =
 functor (O:MiniOrderedType) ->
 struct
  type t = O.t

  (** val compare : t -> t -> t coq_Compare **)

  let compare =
    O.compare

  (** val eq_dec : t -> t -> bool **)

  let eq_dec x y =
    match compare x y with
    | EQ -> true
    | _ -> false
 end

module OrderedTypeFacts =
 functor (O:OrderedType) ->
 struct
  module TO =
   struct
    type t = O.t
   end

  module IsTO =
   struct
   end

  module OrderTac = MakeOrderTac(TO)(IsTO)

  (** val eq_dec : O.t -> O.t -> bool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> bool **)

  let lt_dec x y =
    match O.compare x y with
    | LT -> true
    | _ -> false

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    if eq_dec x y then true else false
 end

module KeyOrderedType =
 functor (O:OrderedType) ->
 struct
  module MO = OrderedTypeFacts(O)
 end
