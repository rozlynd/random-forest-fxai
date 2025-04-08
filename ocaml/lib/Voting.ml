open Datatypes
open FMapInterface
open FMapList
open List0
open PeanoNat

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Voting =
 functor (OT:Orders.UsualOrderedType) ->
 struct
  module OTF = Orders.OT_to_Full(OT)

  module MOT_alt =
   struct
    type t = OTF.t

    type eq = __

    type lt = __

    (** val eq_refl : __ **)

    let eq_refl =
      __

    (** val eq_sym : __ **)

    let eq_sym =
      __

    (** val eq_trans : __ **)

    let eq_trans =
      __

    (** val lt_trans : __ **)

    let lt_trans =
      __

    (** val lt_not_eq : __ **)

    let lt_not_eq =
      __

    (** val compare : OTF.t -> OTF.t -> OTF.t OrderedType.coq_Compare **)

    let compare x y =
      match coq_CompSpec2Type x y (OTF.compare x y) with
      | CompEqT -> OrderedType.EQ
      | CompLtT -> OrderedType.LT
      | CompGtT -> OrderedType.GT
   end

  module OT_alt = OrderedType.MOT_to_OT(MOT_alt)

  module TMap = Make(OT_alt)

  (** val count_occ : OTF.t list -> OTF.t -> int **)

  let count_occ =
    count_occ OTF.eq_dec

  type map = int TMap.t

  type t = OTF.t

  (** val count_all_occ : t list -> map -> map **)

  let rec count_all_occ l acc =
    match l with
    | [] -> acc
    | x :: t0 ->
      (match TMap.find x acc with
       | Some n -> count_all_occ t0 (TMap.add x (Stdlib.Int.succ n) acc)
       | None -> count_all_occ t0 (TMap.add x (Stdlib.Int.succ 0) acc))

  (** val find_max_fold_f : t -> int -> (t * int) -> t * int **)

  let find_max_fold_f k' n' = function
  | (k, n) -> if Nat.ltb n n' then (k', n') else (k, n)

  (** val find_max : map -> t -> t * int **)

  let find_max m default =
    TMap.fold find_max_fold_f m (default, 0)

  (** val vote : t -> t list -> t **)

  let vote x l =
    let (x0, _) = find_max (count_all_occ (x :: l) TMap.empty) x in x0

  (** val vote_In : __ **)

  let vote_In =
    __

  (** val vote_count_le : __ **)

  let vote_count_le =
    __

  (** val vote_count_max : __ **)

  let vote_count_max =
    __
 end
