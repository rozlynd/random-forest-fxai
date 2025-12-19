open MSetInterface
open MSetList
open Orders
open OrdersEx

module StringOT = String_as_OT

module StringOTF = OT_to_Full(StringOT)

module StringSet = Make(StringOT)

type 'a nelist =
| Coq_necons of 'a * 'a list

type fin =
| F1 of int
| FS of int * fin

(** val to_nat : int -> fin -> int **)

let rec to_nat _ = function
| F1 _ -> 0
| FS (n0, p0) -> Stdlib.Int.succ (to_nat n0 p0)

(** val to_fin : int -> int -> fin option **)

let rec to_fin n i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Some (F1 n0))
      (fun i0 ->
      match to_fin n0 i0 with
      | Some p -> Some (FS (n0, p))
      | None -> None)
      i)
    n

(** val to_fin' : int -> int -> fin **)

let to_fin' n pat =
  match to_fin n pat with
  | Some p -> p
  | None -> assert false (* absurd case *)
