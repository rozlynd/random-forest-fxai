open Ascii
open BinNat
open Bool
open Datatypes
open Decimal
open Hexadecimal
open Number

type __ = Obj.t

module N_as_OT = N

module Ascii_as_OT =
 struct
  (** val compare : char -> char -> comparison **)

  let compare a b =
    N_as_OT.compare (coq_N_of_ascii a) (coq_N_of_ascii b)
 end

module String_as_OT =
 struct
  type t = string

  (** val eqb : string -> string -> bool **)

  let eqb =
    (=)

  (** val eq_dec : string -> string -> bool **)

  let eq_dec x y =
    let b = (=) x y in if b then true else false

  (** val compare : string -> string -> comparison **)

  let rec compare a b =
    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

      (fun _ ->
      (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

        (fun _ -> Eq)
        (fun _ _ -> Lt)
        b)
      (fun a_head a_tail ->
      (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

        (fun _ -> Gt)
        (fun b_head b_tail ->
        match Ascii_as_OT.compare a_head b_head with
        | Eq -> compare a_tail b_tail
        | x -> x)
        b)
      a
 end
