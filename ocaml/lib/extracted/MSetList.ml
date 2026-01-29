open Basics
open Datatypes
open List0
open MSetInterface
open Orders
open OrdersFacts
open OrdersLists

module MakeRaw =
 functor (X:OrderedType) ->
 struct
  module MX = OrderedTypeFacts(X)

  module ML = OrderedTypeLists(X)

  type elt = X.t

  type t = elt list

  (** val empty : t **)

  let empty =
    []

  (** val is_empty : t -> bool **)

  let is_empty = function
  | [] -> true
  | _ :: _ -> false

  (** val mem : X.t -> X.t list -> bool **)

  let rec mem x = function
  | [] -> false
  | y :: l ->
    (match X.compare x y with
     | Eq -> true
     | Lt -> false
     | Gt -> mem x l)

  (** val add : X.t -> X.t list -> X.t list **)

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

  (** val remove : X.t -> X.t list -> t **)

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
       | x' :: l' -> (match X.compare x x' with
                      | Eq -> equal l l'
                      | _ -> false))

  (** val subset : X.t list -> X.t list -> bool **)

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

  (** val compare : X.t list -> X.t list -> comparison **)

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

  (** val inf : X.t -> X.t list -> bool **)

  let inf x = function
  | [] -> true
  | y :: _ -> (match X.compare x y with
               | Lt -> true
               | _ -> false)

  (** val isok : X.t list -> bool **)

  let rec isok = function
  | [] -> true
  | x :: l0 -> (&&) (inf x l0) (isok l0)

  module L = MakeListOrdering(X)
 end

module Make =
 functor (X:OrderedType) ->
 struct
  module Raw = MakeRaw(X)

  module E =
   struct
    type t = X.t

    (** val compare : t -> t -> comparison **)

    let compare =
      X.compare

    (** val eq_dec : t -> t -> bool **)

    let eq_dec =
      X.eq_dec
   end

  type elt = X.t

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  (** val this : t_ -> Raw.t **)

  let this t0 =
    t0

  type t = t_

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

  (** val eq_dec : t -> t -> bool **)

  let eq_dec s0 s'0 =
    let b = Raw.equal s0 s'0 in if b then true else false

  (** val compare : t -> t -> comparison **)

  let compare =
    Raw.compare

  (** val min_elt : t -> elt option **)

  let min_elt =
    Raw.min_elt

  (** val max_elt : t -> elt option **)

  let max_elt =
    Raw.max_elt
 end
