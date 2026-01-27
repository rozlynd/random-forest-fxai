
module type UsualDecidableType =
 sig
  type t

  val eq_dec : t -> t -> bool
 end
