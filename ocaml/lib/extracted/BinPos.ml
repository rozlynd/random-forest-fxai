open BinPosDef
open Datatypes
open Decimal
open Hexadecimal
open Nat

module Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Stdlib.Int.succ

  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p q))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  (** val pred_N : int -> int **)

  let pred_N x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> ((fun p->2*p) p))
      (fun p -> (pred_double p))
      (fun _ -> 0)
      x

  type mask = Pos.mask =
  | IsNul
  | IsPos of int
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos 1
  | IsPos p -> IsPos ((fun p->1+2*p) p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos ((fun p->2*p) p)
  | x0 -> x0

  (** val double_pred_mask : int -> mask **)

  let double_pred_mask x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> IsPos ((fun p->2*p) ((fun p->2*p) p)))
      (fun p -> IsPos ((fun p->2*p) (pred_double p)))
      (fun _ -> IsNul)
      x

  (** val sub_mask : int -> int -> mask **)

  let rec sub_mask x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double_mask (sub_mask p q))
        (fun q -> succ_double_mask (sub_mask p q))
        (fun _ -> IsPos ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun q -> double_mask (sub_mask p q))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> IsNeg)
        (fun _ -> IsNeg)
        (fun _ -> IsNul)
        y)
      x

  (** val sub_mask_carry : int -> int -> mask **)

  and sub_mask_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun q -> double_mask (sub_mask p q))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double_mask (sub_mask_carry p q))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun _ -> double_pred_mask p)
        y)
      (fun _ -> IsNeg)
      x

  (** val sub : int -> int -> int **)

  let sub = fun n m -> Stdlib.max 1 (n-m)

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

  (** val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1 **)

  let rec iter f x n =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun n' -> f (iter f (iter f x n') n'))
      (fun n' -> iter f (iter f x n') n')
      (fun _ -> f x)
      n

  (** val pow : int -> int -> int **)

  let pow x =
    iter (mul x) 1

  (** val square : int -> int **)

  let rec square p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> (fun p->1+2*p) ((fun p->2*p)
      (add (square p0) p0)))
      (fun p0 -> (fun p->2*p) ((fun p->2*p) (square p0)))
      (fun _ -> 1)
      p

  (** val size_nat : int -> int **)

  let rec size_nat p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> Stdlib.Int.succ (size_nat p0))
      (fun p0 -> Stdlib.Int.succ (size_nat p0))
      (fun _ -> Stdlib.Int.succ 0)
      p

  (** val size : int -> int **)

  let rec size p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> succ (size p0))
      (fun p0 -> succ (size p0))
      (fun _ -> 1)
      p

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont = fun c x y -> if x=y then c else if x<y then Lt else Gt

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val eqb : int -> int -> bool **)

  let rec eqb p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        (fun _ -> false)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q)
      p

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val sqrtrem_step :
      (int -> int) -> (int -> int) -> (int * mask) -> int * mask **)

  let sqrtrem_step f g = function
  | (s, y) ->
    (match y with
     | IsPos r ->
       let s' = (fun p->1+2*p) ((fun p->2*p) s) in
       let r' = g (f r) in
       if leb s' r'
       then (((fun p->1+2*p) s), (sub_mask r' s'))
       else (((fun p->2*p) s), (IsPos r'))
     | _ ->
       (((fun p->2*p) s),
         (sub_mask (g (f 1)) ((fun p->2*p) ((fun p->2*p) 1)))))

  (** val sqrtrem : int -> int * mask **)

  let rec sqrtrem p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->1+2*p) x) (fun x -> (fun p->1+2*p) x)
          (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->2*p) x) (fun x -> (fun p->1+2*p) x)
          (sqrtrem p1))
        (fun _ -> (1, (IsPos ((fun p->2*p) 1))))
        p0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->1+2*p) x) (fun x -> (fun p->2*p) x)
          (sqrtrem p1))
        (fun p1 ->
        sqrtrem_step (fun x -> (fun p->2*p) x) (fun x -> (fun p->2*p) x)
          (sqrtrem p1))
        (fun _ -> (1, (IsPos 1)))
        p0)
      (fun _ -> (1, IsNul))
      p

  (** val sqrt : int -> int **)

  let sqrt p =
    fst (sqrtrem p)

  (** val gcdn : int -> int -> int -> int **)

  let rec gcdn n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun n0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun a' ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun b' ->
          match compare a' b' with
          | Eq -> a
          | Lt -> gcdn n0 (sub b' a') a
          | Gt -> gcdn n0 (sub a' b') b)
          (fun b0 -> gcdn n0 a b0)
          (fun _ -> 1)
          b)
        (fun a0 ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun _ -> gcdn n0 a0 b)
          (fun b0 -> (fun p->2*p) (gcdn n0 a0 b0))
          (fun _ -> 1)
          b)
        (fun _ -> 1)
        a)
      n

  (** val gcd : int -> int -> int **)

  let gcd a b =
    gcdn (Nat.add (size_nat a) (size_nat b)) a b

  (** val ggcdn : int -> int -> int -> int * (int * int) **)

  let rec ggcdn n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (1, (a, b)))
      (fun n0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun a' ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun b' ->
          match compare a' b' with
          | Eq -> (a, (1, 1))
          | Lt ->
            let (g, p) = ggcdn n0 (sub b' a') a in
            let (ba, aa) = p in (g, (aa, (add aa ((fun p->2*p) ba))))
          | Gt ->
            let (g, p) = ggcdn n0 (sub a' b') b in
            let (ab, bb) = p in (g, ((add bb ((fun p->2*p) ab)), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a b0 in
          let (aa, bb) = p in (g, (aa, ((fun p->2*p) bb))))
          (fun _ -> (1, (a, 1)))
          b)
        (fun a0 ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun _ ->
          let (g, p) = ggcdn n0 a0 b in
          let (aa, bb) = p in (g, (((fun p->2*p) aa), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a0 b0 in (((fun p->2*p) g), p))
          (fun _ -> (1, (a, 1)))
          b)
        (fun _ -> (1, (1, b)))
        a)
      n

  (** val ggcd : int -> int -> int * (int * int) **)

  let ggcd a b =
    ggcdn (Nat.add (size_nat a) (size_nat b)) a b

  (** val coq_Nsucc_double : int -> int **)

  let coq_Nsucc_double x =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      x

  (** val coq_Ndouble : int -> int **)

  let coq_Ndouble n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      n

  (** val coq_lor : int -> int -> int **)

  let rec coq_lor p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun _ -> p)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun q0 -> (fun p->2*p) (coq_lor p0 q0))
        (fun _ -> (fun p->1+2*p) p0)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> q)
        (fun q0 -> (fun p->1+2*p) q0)
        (fun _ -> q)
        q)
      p

  (** val coq_land : int -> int -> int **)

  let rec coq_land p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Nsucc_double (coq_land p0 q0))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun _ -> 1)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun _ -> 0)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> 1)
        (fun _ -> 0)
        (fun _ -> 1)
        q)
      p

  (** val ldiff : int -> int -> int **)

  let rec ldiff p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun q0 -> coq_Nsucc_double (ldiff p0 q0))
        (fun _ -> ((fun p->2*p) p0))
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun _ -> p)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> 0)
        (fun _ -> 1)
        (fun _ -> 0)
        q)
      p

  (** val coq_lxor : int -> int -> int **)

  let rec coq_lxor p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (coq_lxor p0 q0))
        (fun q0 -> coq_Nsucc_double (coq_lxor p0 q0))
        (fun _ -> ((fun p->2*p) p0))
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Nsucc_double (coq_lxor p0 q0))
        (fun q0 -> coq_Ndouble (coq_lxor p0 q0))
        (fun _ -> ((fun p->1+2*p) p0))
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> ((fun p->2*p) q0))
        (fun q0 -> ((fun p->1+2*p) q0))
        (fun _ -> 0)
        q)
      p

  (** val shiftl : int -> int -> int **)

  let shiftl p n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> p)
      (fun n0 -> iter (fun x -> (fun p->2*p) x) p n0)
      n

  (** val testbit_nat : int -> int -> bool **)

  let rec testbit_nat p n =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> true)
        (fun n' -> testbit_nat p0 n')
        n)
      (fun p0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun n' -> testbit_nat p0 n')
        n)
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> true)
        (fun _ -> false)
        n)
      p

  (** val testbit : int -> int -> bool **)

  let rec testbit p n =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> true)
        (fun n0 -> testbit p0 (pred_N n0))
        n)
      (fun p0 ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> false)
        (fun n0 -> testbit p0 (pred_N n0))
        n)
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> true)
        (fun _ -> false)
        n)
      p

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> op a (iter_op op p0 (op a a)))
      (fun p0 -> iter_op op p0 (op a a))
      (fun _ -> a)
      p

  (** val to_nat : int -> int **)

  let to_nat x =
    iter_op Nat.add x (Stdlib.Int.succ 0)

  (** val of_succ_nat : int -> int **)

  let rec of_succ_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun x -> succ (of_succ_nat x))
      n

  (** val of_uint_acc : Decimal.uint -> int -> int **)

  let rec of_uint_acc d acc =
    match d with
    | Decimal.Nil -> acc
    | Decimal.D0 l ->
      of_uint_acc l (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc)
    | Decimal.D1 l ->
      of_uint_acc l
        (add 1 (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))
    | Decimal.D2 l ->
      of_uint_acc l
        (add ((fun p->2*p) 1)
          (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))
    | Decimal.D3 l ->
      of_uint_acc l
        (add ((fun p->1+2*p) 1)
          (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))
    | Decimal.D4 l ->
      of_uint_acc l
        (add ((fun p->2*p) ((fun p->2*p) 1))
          (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))
    | Decimal.D5 l ->
      of_uint_acc l
        (add ((fun p->1+2*p) ((fun p->2*p) 1))
          (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))
    | Decimal.D6 l ->
      of_uint_acc l
        (add ((fun p->2*p) ((fun p->1+2*p) 1))
          (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))
    | Decimal.D7 l ->
      of_uint_acc l
        (add ((fun p->1+2*p) ((fun p->1+2*p) 1))
          (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))
    | Decimal.D8 l ->
      of_uint_acc l
        (add ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
          (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))
    | Decimal.D9 l ->
      of_uint_acc l
        (add ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))
          (mul ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))) acc))

  (** val of_uint : Decimal.uint -> int **)

  let rec of_uint = function
  | Decimal.Nil -> 0
  | Decimal.D0 l -> of_uint l
  | Decimal.D1 l -> (of_uint_acc l 1)
  | Decimal.D2 l -> (of_uint_acc l ((fun p->2*p) 1))
  | Decimal.D3 l -> (of_uint_acc l ((fun p->1+2*p) 1))
  | Decimal.D4 l -> (of_uint_acc l ((fun p->2*p) ((fun p->2*p) 1)))
  | Decimal.D5 l -> (of_uint_acc l ((fun p->1+2*p) ((fun p->2*p) 1)))
  | Decimal.D6 l -> (of_uint_acc l ((fun p->2*p) ((fun p->1+2*p) 1)))
  | Decimal.D7 l -> (of_uint_acc l ((fun p->1+2*p) ((fun p->1+2*p) 1)))
  | Decimal.D8 l ->
    (of_uint_acc l ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
  | Decimal.D9 l ->
    (of_uint_acc l ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))

  (** val of_hex_uint_acc : uint -> int -> int **)

  let rec of_hex_uint_acc d acc =
    match d with
    | Nil -> acc
    | D0 l ->
      of_hex_uint_acc l
        (mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
          acc)
    | D1 l ->
      of_hex_uint_acc l
        (add 1
          (mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
            acc))
    | D2 l ->
      of_hex_uint_acc l
        (add ((fun p->2*p) 1)
          (mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
            acc))
    | D3 l ->
      of_hex_uint_acc l
        (add ((fun p->1+2*p) 1)
          (mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
            acc))
    | D4 l ->
      of_hex_uint_acc l
        (add ((fun p->2*p) ((fun p->2*p) 1))
          (mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
            acc))
    | D5 l ->
      of_hex_uint_acc l
        (add ((fun p->1+2*p) ((fun p->2*p) 1))
          (mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
            acc))
    | D6 l ->
      of_hex_uint_acc l
        (add ((fun p->2*p) ((fun p->1+2*p) 1))
          (mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
            acc))
    | D7 l ->
      of_hex_uint_acc l
        (add ((fun p->1+2*p) ((fun p->1+2*p) 1))
          (mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
            acc))
    | D8 l ->
      of_hex_uint_acc l
        (add ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
          (mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
            acc))
    | D9 l ->
      of_hex_uint_acc l
        (add ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))
          (mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
            acc))
    | Da l ->
      of_hex_uint_acc l
        (add ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))
          (mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
            acc))
    | Db l ->
      of_hex_uint_acc l
        (add ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))
          (mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
            acc))
    | Dc l ->
      of_hex_uint_acc l
        (add ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))
          (mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
            acc))
    | Dd l ->
      of_hex_uint_acc l
        (add ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))
          (mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
            acc))
    | De l ->
      of_hex_uint_acc l
        (add ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))
          (mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
            acc))
    | Df l ->
      of_hex_uint_acc l
        (add ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))
          (mul ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
            acc))

  (** val of_hex_uint : uint -> int **)

  let rec of_hex_uint = function
  | Nil -> 0
  | D0 l -> of_hex_uint l
  | D1 l -> (of_hex_uint_acc l 1)
  | D2 l -> (of_hex_uint_acc l ((fun p->2*p) 1))
  | D3 l -> (of_hex_uint_acc l ((fun p->1+2*p) 1))
  | D4 l -> (of_hex_uint_acc l ((fun p->2*p) ((fun p->2*p) 1)))
  | D5 l -> (of_hex_uint_acc l ((fun p->1+2*p) ((fun p->2*p) 1)))
  | D6 l -> (of_hex_uint_acc l ((fun p->2*p) ((fun p->1+2*p) 1)))
  | D7 l -> (of_hex_uint_acc l ((fun p->1+2*p) ((fun p->1+2*p) 1)))
  | D8 l -> (of_hex_uint_acc l ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
  | D9 l ->
    (of_hex_uint_acc l ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))
  | Da l ->
    (of_hex_uint_acc l ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))
  | Db l ->
    (of_hex_uint_acc l ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))
  | Dc l ->
    (of_hex_uint_acc l ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))
  | Dd l ->
    (of_hex_uint_acc l ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))
  | De l ->
    (of_hex_uint_acc l ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))
  | Df l ->
    (of_hex_uint_acc l ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))))

  (** val to_little_uint : int -> Decimal.uint **)

  let rec to_little_uint p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> Decimal.Little.succ_double (to_little_uint p0))
      (fun p0 -> Decimal.Little.double (to_little_uint p0))
      (fun _ -> Decimal.D1 Decimal.Nil)
      p

  (** val to_uint : int -> Decimal.uint **)

  let to_uint p =
    Decimal.rev (to_little_uint p)

  (** val to_little_hex_uint : int -> uint **)

  let rec to_little_hex_uint p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> Little.succ_double (to_little_hex_uint p0))
      (fun p0 -> Little.double (to_little_hex_uint p0))
      (fun _ -> D1 Nil)
      p

  (** val to_hex_uint : int -> uint **)

  let to_hex_uint p =
    rev (to_little_hex_uint p)

  (** val eq_dec : int -> int -> bool **)

  let rec eq_dec p x0 =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        (fun _ -> false)
        x0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        x0)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        x0)
      p

  (** val peano_rect : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1 **)

  let rec peano_rect a f p =
    let f2 =
      peano_rect (f 1 a) (fun p0 x ->
        f (succ ((fun p->2*p) p0)) (f ((fun p->2*p) p0) x))
    in
    ((fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
       (fun q -> f ((fun p->2*p) q) (f2 q))
       (fun q -> f2 q)
       (fun _ -> a)
       p)
 end
