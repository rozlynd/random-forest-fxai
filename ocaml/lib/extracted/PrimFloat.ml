
(** val abs : Float64.t -> Float64.t **)

let abs = Float64.abs

(** val eqb : Float64.t -> Float64.t -> bool **)

let eqb = Float64.eq

(** val ltb : Float64.t -> Float64.t -> bool **)

let ltb = Float64.lt

(** val leb : Float64.t -> Float64.t -> bool **)

let leb = Float64.le

(** val div : Float64.t -> Float64.t -> Float64.t **)

let div = Float64.div

(** val next_down : Float64.t -> Float64.t **)

let next_down = Float64.next_down

(** val infinity : Float64.t **)

let infinity =
  (Float64.of_float (infinity))

(** val neg_infinity : Float64.t **)

let neg_infinity =
  (Float64.of_float (neg_infinity))

(** val one : Float64.t **)

let one =
  (Float64.of_float (0x1p+0))

(** val zero : Float64.t **)

let zero =
  (Float64.of_float (0x0p+0))

(** val is_zero : Float64.t -> bool **)

let is_zero f =
  eqb f zero

(** val is_infinity : Float64.t -> bool **)

let is_infinity f =
  eqb (abs f) infinity

(** val get_sign : Float64.t -> bool **)

let get_sign f =
  let f0 = if is_zero f then div one f else f in ltb f0 zero
