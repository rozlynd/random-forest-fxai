open BinPos
open Bool
open Datatypes
open Decimal
open Hexadecimal
open Number

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module N =
 struct
  type t = int

  (** val zero : int **)

  let zero =
    0

  (** val one : int **)

  let one =
    1

  (** val two : int **)

  let two =
    ((fun p->2*p) 1)

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      x

  (** val double : int -> int **)

  let double n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      n

  (** val succ : int -> int **)

  let succ = Stdlib.Int.succ

  (** val pred : int -> int **)

  let pred = fun n -> Stdlib.Int.max 0 (n-1)

  (** val succ_pos : int -> int **)

  let succ_pos n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> Pos.succ p)
      n

  (** val add : int -> int -> int **)

  let add = (+)

  (** val sub : int -> int -> int **)

  let sub = fun n m -> Stdlib.Int.max 0 (n-m)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val eqb : int -> int -> bool **)

  let eqb n m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> true)
        (fun _ -> false)
        m)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> false)
        (fun q -> Pos.eqb p q)
        m)
      n

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val min : int -> int -> int **)

  let min = Stdlib.min

  (** val max : int -> int -> int **)

  let max = Stdlib.max

  (** val div2 : int -> int **)

  let div2 n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p -> p)
        (fun p -> p)
        (fun _ -> 0)
        p0)
      n

  (** val even : int -> bool **)

  let even n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> true)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> true)
        (fun _ -> false)
        p)
      n

  (** val odd : int -> bool **)

  let odd n =
    negb (even n)

  (** val pow : int -> int -> int **)

  let pow n p =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p0 ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> 0)
        (fun q -> (Pos.pow q p0))
        n)
      p

  (** val square : int -> int **)

  let square n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> (Pos.square p))
      n

  (** val log2 : int -> int **)

  let log2 n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p -> (Pos.size p))
        (fun p -> (Pos.size p))
        (fun _ -> 0)
        p0)
      n

  (** val size : int -> int **)

  let size n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> (Pos.size p))
      n

  (** val size_nat : int -> int **)

  let size_nat n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> Pos.size_nat p)
      n

  (** val pos_div_eucl : int -> int -> int * int **)

  let rec pos_div_eucl a b =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r'))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r'))
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> (0, 1))
        (fun p ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun _ -> (0, 1))
          (fun _ -> (0, 1))
          (fun _ -> (1, 0))
          p)
        b)
      a

  (** val div_eucl : int -> int -> int * int **)

  let div_eucl a b =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> (0, 0))
      (fun na ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> (0, a))
        (fun _ -> pos_div_eucl na b)
        b)
      a

  (** val div : int -> int -> int **)

  let div = fun a b -> if b=0 then 0 else a/b

  (** val modulo : int -> int -> int **)

  let modulo = fun a b -> if b=0 then a else a mod b

  (** val gcd : int -> int -> int **)

  let gcd a b =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> b)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> a)
        (fun q -> (Pos.gcd p q))
        b)
      a

  (** val ggcd : int -> int -> int * (int * int) **)

  let ggcd a b =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> (b, (0, 1)))
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> (a, (1, 0)))
        (fun q ->
        let (g, p0) = Pos.ggcd p q in let (aa, bb) = p0 in (g, (aa, bb)))
        b)
      a

  (** val sqrtrem : int -> int * int **)

  let sqrtrem n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> (0, 0))
      (fun p ->
      let (s, m) = Pos.sqrtrem p in
      (match m with
       | Pos.IsPos r -> (s, r)
       | _ -> (s, 0)))
      n

  (** val sqrt : int -> int **)

  let sqrt n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> (Pos.sqrt p))
      n

  (** val coq_lor : int -> int -> int **)

  let coq_lor n m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> m)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> n)
        (fun q -> (Pos.coq_lor p q))
        m)
      n

  (** val coq_land : int -> int -> int **)

  let coq_land n m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> 0)
        (fun q -> Pos.coq_land p q)
        m)
      n

  (** val ldiff : int -> int -> int **)

  let ldiff n m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> n)
        (fun q -> Pos.ldiff p q)
        m)
      n

  (** val coq_lxor : int -> int -> int **)

  let coq_lxor n m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> m)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> n)
        (fun q -> Pos.coq_lxor p q)
        m)
      n

  (** val shiftl_nat : int -> int -> int **)

  let rec shiftl_nat a n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> a)
      (fun n0 -> double (shiftl_nat a n0))
      n

  (** val shiftr_nat : int -> int -> int **)

  let rec shiftr_nat a n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> a)
      (fun n0 -> div2 (shiftr_nat a n0))
      n

  (** val shiftl : int -> int -> int **)

  let shiftl a n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun a0 -> (Pos.shiftl a0 n))
      a

  (** val shiftr : int -> int -> int **)

  let shiftr a n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> a)
      (fun p -> Pos.iter div2 a p)
      n

  (** val testbit_nat : int -> int -> bool **)

  let testbit_nat a =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ _ -> false)
      (fun p -> Pos.testbit_nat p)
      a

  (** val testbit : int -> int -> bool **)

  let testbit a n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> false)
      (fun p -> Pos.testbit p n)
      a

  (** val to_nat : int -> int **)

  let to_nat a =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> Pos.to_nat p)
      a

  (** val of_nat : int -> int **)

  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' -> (Pos.of_succ_nat n'))
      n

  (** val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let iter n f x =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> x)
      (fun p -> Pos.iter f x p)
      n

  (** val of_uint : Decimal.uint -> int **)

  let of_uint =
    Pos.of_uint

  (** val of_hex_uint : Hexadecimal.uint -> int **)

  let of_hex_uint =
    Pos.of_hex_uint

  (** val of_num_uint : uint -> int **)

  let of_num_uint = function
  | UIntDecimal d0 -> of_uint d0
  | UIntHexadecimal d0 -> of_hex_uint d0

  (** val of_int : Decimal.signed_int -> int option **)

  let of_int d =
    match Decimal.norm d with
    | Decimal.Pos d0 -> Some (Pos.of_uint d0)
    | Decimal.Neg _ -> None

  (** val of_hex_int : Hexadecimal.signed_int -> int option **)

  let of_hex_int d =
    match norm d with
    | Pos d0 -> Some (Pos.of_hex_uint d0)
    | Neg _ -> None

  (** val of_num_int : signed_int -> int option **)

  let of_num_int = function
  | IntDecimal d0 -> of_int d0
  | IntHexadecimal d0 -> of_hex_int d0

  (** val to_uint : int -> Decimal.uint **)

  let to_uint n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> Decimal.D0 Decimal.Nil)
      (fun p -> Pos.to_uint p)
      n

  (** val to_hex_uint : int -> Hexadecimal.uint **)

  let to_hex_uint n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> D0 Nil)
      (fun p -> Pos.to_hex_uint p)
      n

  (** val to_num_uint : int -> uint **)

  let to_num_uint n =
    UIntDecimal (to_uint n)

  (** val to_num_hex_uint : int -> uint **)

  let to_num_hex_uint n =
    UIntHexadecimal (to_hex_uint n)

  (** val to_int : int -> Decimal.signed_int **)

  let to_int n =
    Decimal.Pos (to_uint n)

  (** val to_hex_int : int -> Hexadecimal.signed_int **)

  let to_hex_int n =
    Pos (to_hex_uint n)

  (** val to_num_int : int -> signed_int **)

  let to_num_int n =
    IntDecimal (to_int n)

  (** val to_num_hex_int : int -> signed_int **)

  let to_num_hex_int n =
    IntHexadecimal (to_hex_int n)

  (** val eq_dec : int -> int -> bool **)

  let eq_dec n m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> true)
        (fun _ -> false)
        m)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> false)
        (fun p0 -> Pos.eq_dec p p0)
        m)
      n

  (** val discr : int -> int option **)

  let discr n =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> None)
      (fun p -> Some p)
      n

  (** val binary_rect :
      'a1 -> (int -> 'a1 -> 'a1) -> (int -> 'a1 -> 'a1) -> int -> 'a1 **)

  let binary_rect f0 f2 fS2 n =
    let f2' = fun p -> f2 p in
    let fS2' = fun p -> fS2 p in
    ((fun f0 fp n -> if n=0 then f0 () else fp n)
       (fun _ -> f0)
       (fun p ->
       let rec f p0 =
         (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
           (fun p1 -> fS2' p1 (f p1))
           (fun p1 -> f2' p1 (f p1))
           (fun _ -> fS2 0 f0)
           p0
       in f p)
       n)

  (** val binary_rec :
      'a1 -> (int -> 'a1 -> 'a1) -> (int -> 'a1 -> 'a1) -> int -> 'a1 **)

  let binary_rec =
    binary_rect

  (** val peano_rect : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1 **)

  let peano_rect f0 f n =
    let f' = fun p -> f p in
    ((fun f0 fp n -> if n=0 then f0 () else fp n)
       (fun _ -> f0)
       (fun p -> Pos.peano_rect (f 0 f0) f' p)
       n)

  (** val peano_rec : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1 **)

  let peano_rec =
    peano_rect

  (** val recursion : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1 **)

  let recursion =
    peano_rect

  (** val leb_spec0 : int -> int -> reflect **)

  let leb_spec0 x y =
    iff_reflect (leb x y)

  (** val ltb_spec0 : int -> int -> reflect **)

  let ltb_spec0 x y =
    iff_reflect (ltb x y)

  module Private_OrderTac =
   struct
    module IsTotal =
     struct
     end

    module Tac =
     struct
     end
   end

  (** val measure_right_induction :
      ('a1 -> int) -> int -> ('a1 -> __ -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1
      -> 'a2 **)

  let measure_right_induction f _ iH x =
    let t0 = f x in
    let rec f0 _ y =
      iH y __ (fun y' _ -> let y0 = f y' in f0 y0 y')
    in f0 t0 x

  (** val measure_left_induction :
      ('a1 -> int) -> int -> ('a1 -> __ -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1
      -> 'a2 **)

  let measure_left_induction f _ iH x =
    let t0 = f x in
    let rec f0 _ y =
      iH y __ (fun y' _ -> let y0 = f y' in f0 y0 y')
    in f0 t0 x

  (** val measure_induction :
      ('a1 -> int) -> ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

  let measure_induction f iH x =
    measure_right_induction f 0 (fun y _ iH' -> iH y (fun y0 _ -> iH' y0 __))
      x

  module Private_Tac =
   struct
   end

  module Private_Dec =
   struct
    (** val max_case_strong :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__
        -> 'a1) -> 'a1 **)

    let max_case_strong n m compat hl hr =
      let c = coq_CompSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat n (max n m) __ (hl __)
       | _ -> compat m (max n m) __ (hr __))

    (** val max_case :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let max_case n m x x0 x1 =
      max_case_strong n m x (fun _ -> x0) (fun _ -> x1)

    (** val max_dec : int -> int -> bool **)

    let max_dec n m =
      max_case n m (fun _ _ _ h0 -> h0) true false

    (** val min_case_strong :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__
        -> 'a1) -> 'a1 **)

    let min_case_strong n m compat hl hr =
      let c = coq_CompSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat m (min n m) __ (hr __)
       | _ -> compat n (min n m) __ (hl __))

    (** val min_case :
        int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let min_case n m x x0 x1 =
      min_case_strong n m x (fun _ -> x0) (fun _ -> x1)

    (** val min_dec : int -> int -> bool **)

    let min_dec n m =
      min_case n m (fun _ _ _ h0 -> h0) true false
   end

  (** val max_case_strong :
      int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let max_case_strong n m x x0 =
    Private_Dec.max_case_strong n m (fun _ _ _ x1 -> x1) x x0

  (** val max_case : int -> int -> 'a1 -> 'a1 -> 'a1 **)

  let max_case n m x x0 =
    max_case_strong n m (fun _ -> x) (fun _ -> x0)

  (** val max_dec : int -> int -> bool **)

  let max_dec =
    Private_Dec.max_dec

  (** val min_case_strong :
      int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let min_case_strong n m x x0 =
    Private_Dec.min_case_strong n m (fun _ _ _ x1 -> x1) x x0

  (** val min_case : int -> int -> 'a1 -> 'a1 -> 'a1 **)

  let min_case n m x x0 =
    min_case_strong n m (fun _ -> x) (fun _ -> x0)

  (** val min_dec : int -> int -> bool **)

  let min_dec =
    Private_Dec.min_dec

  module Private_NZPow =
   struct
   end

  module Private_NZSqrt =
   struct
   end

  (** val sqrt_up : int -> int **)

  let sqrt_up a =
    match compare 0 a with
    | Lt -> succ (sqrt (pred a))
    | _ -> 0

  (** val log2_up : int -> int **)

  let log2_up a =
    match compare 1 a with
    | Lt -> succ (log2 (pred a))
    | _ -> 0

  module Private_NZGcdProp =
   struct
   end

  module Private_NDivProp =
   struct
    module Private_NZDiv =
     struct
     end
   end

  module Div0 =
   struct
   end

  module Private_NLcmProp =
   struct
    (** val lcm : int -> int -> int **)

    let lcm a b =
      mul a (div b (gcd a b))
   end

  (** val lcm : int -> int -> int **)

  let lcm a b =
    mul a (div b (gcd a b))

  module Lcm0 =
   struct
   end

  (** val eqb_spec : int -> int -> reflect **)

  let eqb_spec x y =
    iff_reflect (eqb x y)

  (** val b2n : bool -> int **)

  let b2n = function
  | true -> 1
  | false -> 0

  (** val setbit : int -> int -> int **)

  let setbit a n =
    coq_lor a (shiftl 1 n)

  (** val clearbit : int -> int -> int **)

  let clearbit a n =
    ldiff a (shiftl 1 n)

  (** val ones : int -> int **)

  let ones n =
    pred (shiftl 1 n)

  (** val lnot : int -> int -> int **)

  let lnot a n =
    coq_lxor a (ones n)
 end
