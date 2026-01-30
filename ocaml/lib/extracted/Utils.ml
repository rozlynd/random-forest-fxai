open Basics
open Datatypes
open List0
open MSetInterface
open MSetList
open Orders
open OrdersEx
open PeanoNat

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module StringOT = String_as_OT

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

let rec to_fin n0 i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Some (F1 n1))
      (fun i0 ->
      match to_fin n1 i0 with
      | Some p -> Some (FS (n1, p))
      | None -> None)
      i)
    n0

(** val to_fin' : int -> int -> fin **)

let to_fin' n0 pat =
  match to_fin n0 pat with
  | Some p -> p
  | None -> assert false (* absurd case *)

module type FinSig =
 sig
  val n : int
 end

module FinOT =
 functor (S:FinSig) ->
 struct
  type t = fin

  type eq = __

  type lt = __

  (** val compare : fin -> fin -> comparison **)

  let compare m p =
    Nat.compare (to_nat S.n m) (to_nat S.n p)

  (** val eq_equiv : __ **)

  let eq_equiv =
    __

  (** val lt_strorder : __ **)

  let lt_strorder =
    __

  (** val lt_compat : __ **)

  let lt_compat =
    __

  (** val compare_spec : __ **)

  let compare_spec =
    __

  (** val eq_dec : fin -> fin -> bool **)

  let eq_dec m p =
    (=) (to_nat S.n m) (to_nat S.n p)
 end

module type FinSet =
 sig
  val n : int

  module E :
   sig
    type t = fin

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> bool
   end

  type elt = E.t

  type t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> t * t

  val cardinal : t -> int

  val elements : t -> elt list

  val choose : t -> elt option

  val eq_dec : t -> t -> bool

  val compare : t -> t -> comparison

  val min_elt : t -> elt option

  val max_elt : t -> elt option

  val all : t

  val compl : t -> t
 end

module MakeFinSet =
 functor (S:FinSig) ->
 struct
  module X = FinOT(S)

  module Raw =
   struct
    type elt = fin

    type t = elt list

    (** val empty : t **)

    let empty =
      []

    (** val is_empty : t -> bool **)

    let is_empty = function
    | [] -> true
    | _ :: _ -> false

    (** val mem : fin -> fin list -> bool **)

    let rec mem x = function
    | [] -> false
    | y :: l ->
      (match X.compare x y with
       | Eq -> true
       | Lt -> false
       | Gt -> mem x l)

    (** val add : fin -> fin list -> fin list **)

    let rec add x s = match s with
    | [] -> x :: []
    | y :: l ->
      (match X.compare x y with
       | Eq -> s
       | Lt -> x :: s
       | Gt -> y :: (add x l))

    (** val singleton : elt -> elt list **)

    let singleton x =
      x :: []

    (** val remove : fin -> fin list -> t **)

    let rec remove x s = match s with
    | [] -> []
    | y :: l ->
      (match X.compare x y with
       | Eq -> l
       | Lt -> s
       | Gt -> y :: (remove x l))

    (** val union : t -> t -> t **)

    let rec union s = match s with
    | [] -> (fun s' -> s')
    | x :: l ->
      let rec union_aux s' = match s' with
      | [] -> s
      | x' :: l' ->
        (match X.compare x x' with
         | Eq -> x :: (union l l')
         | Lt -> x :: (union l s')
         | Gt -> x' :: (union_aux l'))
      in union_aux

    (** val inter : t -> t -> t **)

    let rec inter = function
    | [] -> (fun _ -> [])
    | x :: l ->
      let rec inter_aux s' = match s' with
      | [] -> []
      | x' :: l' ->
        (match X.compare x x' with
         | Eq -> x :: (inter l l')
         | Lt -> inter l s'
         | Gt -> inter_aux l')
      in inter_aux

    (** val diff : t -> t -> t **)

    let rec diff s = match s with
    | [] -> (fun _ -> [])
    | x :: l ->
      let rec diff_aux s' = match s' with
      | [] -> s
      | x' :: l' ->
        (match X.compare x x' with
         | Eq -> diff l l'
         | Lt -> x :: (diff l s')
         | Gt -> diff_aux l')
      in diff_aux

    (** val equal : t -> t -> bool **)

    let rec equal s s' =
      match s with
      | [] -> (match s' with
               | [] -> true
               | _ :: _ -> false)
      | x :: l ->
        (match s' with
         | [] -> false
         | x' :: l' ->
           (match X.compare x x' with
            | Eq -> equal l l'
            | _ -> false))

    (** val subset : fin list -> fin list -> bool **)

    let rec subset s s' =
      match s with
      | [] -> true
      | x :: l ->
        (match s' with
         | [] -> false
         | x' :: l' ->
           (match X.compare x x' with
            | Eq -> subset l l'
            | Lt -> false
            | Gt -> subset s l'))

    (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

    let fold f s i =
      fold_left (flip f) s i

    (** val filter : (elt -> bool) -> t -> t **)

    let rec filter f = function
    | [] -> []
    | x :: l -> if f x then x :: (filter f l) else filter f l

    (** val for_all : (elt -> bool) -> t -> bool **)

    let rec for_all f = function
    | [] -> true
    | x :: l -> if f x then for_all f l else false

    (** val exists_ : (elt -> bool) -> t -> bool **)

    let rec exists_ f = function
    | [] -> false
    | x :: l -> if f x then true else exists_ f l

    (** val partition : (elt -> bool) -> t -> t * t **)

    let rec partition f = function
    | [] -> ([], [])
    | x :: l ->
      let (s1, s2) = partition f l in
      if f x then ((x :: s1), s2) else (s1, (x :: s2))

    (** val cardinal : t -> int **)

    let cardinal =
      length

    (** val elements : t -> elt list **)

    let elements x =
      x

    (** val min_elt : t -> elt option **)

    let min_elt = function
    | [] -> None
    | x :: _ -> Some x

    (** val max_elt : t -> elt option **)

    let rec max_elt = function
    | [] -> None
    | x :: l -> (match l with
                 | [] -> Some x
                 | _ :: _ -> max_elt l)

    (** val choose : t -> elt option **)

    let choose =
      min_elt

    (** val compare : fin list -> fin list -> comparison **)

    let rec compare s s' =
      match s with
      | [] -> (match s' with
               | [] -> Eq
               | _ :: _ -> Lt)
      | x :: s0 ->
        (match s' with
         | [] -> Gt
         | x' :: s'0 ->
           (match X.compare x x' with
            | Eq -> compare s0 s'0
            | x0 -> x0))
   end

  module E =
   struct
    type t = fin

    (** val compare : fin -> fin -> comparison **)

    let compare =
      X.compare

    (** val eq_dec : fin -> fin -> bool **)

    let eq_dec =
      X.eq_dec
   end

  type elt = fin

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  (** val this : t_ -> Raw.t **)

  let this t0 =
    t0

  type t = t_

  type coq_In = __

  type coq_Equal = __

  type coq_Subset = __

  type coq_Empty = __

  type coq_For_all = __

  type coq_Exists = __

  (** val mem : elt -> t -> bool **)

  let mem =
    Raw.mem

  (** val add : elt -> t -> t **)

  let add =
    Raw.add

  (** val remove : elt -> t -> t **)

  let remove =
    Raw.remove

  (** val singleton : elt -> t **)

  let singleton =
    Raw.singleton

  (** val union : t -> t -> t **)

  let union =
    Raw.union

  (** val inter : t -> t -> t **)

  let inter =
    Raw.inter

  (** val diff : t -> t -> t **)

  let diff =
    Raw.diff

  (** val equal : t -> t -> bool **)

  let equal =
    Raw.equal

  (** val subset : t -> t -> bool **)

  let subset =
    Raw.subset

  (** val empty : t **)

  let empty =
    Raw.empty

  (** val is_empty : t -> bool **)

  let is_empty =
    Raw.is_empty

  (** val elements : t -> elt list **)

  let elements =
    Raw.elements

  (** val choose : t -> elt option **)

  let choose =
    Raw.choose

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold =
    Raw.fold

  (** val cardinal : t -> int **)

  let cardinal =
    Raw.cardinal

  (** val filter : (elt -> bool) -> t -> t **)

  let filter =
    Raw.filter

  (** val for_all : (elt -> bool) -> t -> bool **)

  let for_all =
    Raw.for_all

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let exists_ =
    Raw.exists_

  (** val partition : (elt -> bool) -> t -> t * t **)

  let partition f s =
    let p = Raw.partition f s in ((fst p), (snd p))

  (** val coq_In_compat : __ **)

  let coq_In_compat =
    __

  type eq = __

  (** val eq_equiv : __ **)

  let eq_equiv =
    __

  (** val eq_dec : t -> t -> bool **)

  let eq_dec s0 s'0 =
    let b = Raw.equal s0 s'0 in if b then true else false

  (** val mem_spec : __ **)

  let mem_spec =
    __

  (** val equal_spec : __ **)

  let equal_spec =
    __

  (** val subset_spec : __ **)

  let subset_spec =
    __

  (** val empty_spec : __ **)

  let empty_spec =
    __

  (** val is_empty_spec : __ **)

  let is_empty_spec =
    __

  (** val add_spec : __ **)

  let add_spec =
    __

  (** val remove_spec : __ **)

  let remove_spec =
    __

  (** val singleton_spec : __ **)

  let singleton_spec =
    __

  (** val union_spec : __ **)

  let union_spec =
    __

  (** val inter_spec : __ **)

  let inter_spec =
    __

  (** val diff_spec : __ **)

  let diff_spec =
    __

  (** val fold_spec : __ **)

  let fold_spec =
    __

  (** val cardinal_spec : __ **)

  let cardinal_spec =
    __

  (** val filter_spec : __ **)

  let filter_spec =
    __

  (** val for_all_spec : __ **)

  let for_all_spec =
    __

  (** val exists_spec : __ **)

  let exists_spec =
    __

  (** val partition_spec1 : __ **)

  let partition_spec1 =
    __

  (** val partition_spec2 : __ **)

  let partition_spec2 =
    __

  (** val elements_spec1 : __ **)

  let elements_spec1 =
    __

  (** val elements_spec2w : __ **)

  let elements_spec2w =
    __

  (** val choose_spec1 : __ **)

  let choose_spec1 =
    __

  (** val choose_spec2 : __ **)

  let choose_spec2 =
    __

  (** val compare : t -> t -> comparison **)

  let compare =
    Raw.compare

  (** val min_elt : t -> elt option **)

  let min_elt =
    Raw.min_elt

  (** val max_elt : t -> elt option **)

  let max_elt =
    Raw.max_elt

  type lt = __

  (** val lt_strorder : __ **)

  let lt_strorder =
    __

  (** val lt_compat : __ **)

  let lt_compat =
    __

  (** val compare_spec : __ **)

  let compare_spec =
    __

  (** val elements_spec2 : __ **)

  let elements_spec2 =
    __

  (** val min_elt_spec1 : __ **)

  let min_elt_spec1 =
    __

  (** val min_elt_spec2 : __ **)

  let min_elt_spec2 =
    __

  (** val min_elt_spec3 : __ **)

  let min_elt_spec3 =
    __

  (** val max_elt_spec1 : __ **)

  let max_elt_spec1 =
    __

  (** val max_elt_spec2 : __ **)

  let max_elt_spec2 =
    __

  (** val max_elt_spec3 : __ **)

  let max_elt_spec3 =
    __

  (** val choose_spec3 : __ **)

  let choose_spec3 =
    __

  (** val all_below : int -> t option **)

  let rec all_below n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Some empty)
      (fun n1 ->
      let filtered_var = to_fin S.n n1 in
      (match filtered_var with
       | Some p ->
         let filtered_var0 = all_below n1 in
         (match filtered_var0 with
          | Some s -> Some (add p s)
          | None -> None)
       | None -> None))
      n0

  (** val all_obligation_1 : __ -> t **)

  let all_obligation_1 _ =
    assert false (* absurd case *)

  (** val all : t **)

  let all =
    let filtered_var = all_below S.n in
    (match filtered_var with
     | Some t0 -> t0
     | None -> all_obligation_1 __)

  (** val coq_In_all : __ **)

  let coq_In_all =
    __

  (** val compl : t -> t **)

  let compl s =
    diff all s

  (** val coq_In_compl : __ **)

  let coq_In_compl =
    __

  (** val compl_compat : __ **)

  let compl_compat =
    __
 end
