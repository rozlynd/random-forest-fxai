open BinPos
open Bool
open Datatypes
open Decimal
open Hexadecimal
open Number

type __ = Obj.t

module N :
 sig
  type t = int

  val zero : int

  val one : int

  val two : int

  val succ_double : int -> int

  val double : int -> int

  val succ : int -> int

  val pred : int -> int

  val succ_pos : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val compare : int -> int -> comparison

  val eqb : int -> int -> bool

  val leb : int -> int -> bool

  val ltb : int -> int -> bool

  val min : int -> int -> int

  val max : int -> int -> int

  val div2 : int -> int

  val even : int -> bool

  val odd : int -> bool

  val pow : int -> int -> int

  val square : int -> int

  val log2 : int -> int

  val size : int -> int

  val size_nat : int -> int

  val pos_div_eucl : int -> int -> int * int

  val div_eucl : int -> int -> int * int

  val div : int -> int -> int

  val modulo : int -> int -> int

  val gcd : int -> int -> int

  val ggcd : int -> int -> int * (int * int)

  val sqrtrem : int -> int * int

  val sqrt : int -> int

  val coq_lor : int -> int -> int

  val coq_land : int -> int -> int

  val ldiff : int -> int -> int

  val coq_lxor : int -> int -> int

  val shiftl_nat : int -> int -> int

  val shiftr_nat : int -> int -> int

  val shiftl : int -> int -> int

  val shiftr : int -> int -> int

  val testbit_nat : int -> int -> bool

  val testbit : int -> int -> bool

  val to_nat : int -> int

  val of_nat : int -> int

  val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1

  val of_uint : Decimal.uint -> int

  val of_hex_uint : Hexadecimal.uint -> int

  val of_num_uint : uint -> int

  val of_int : Decimal.signed_int -> int option

  val of_hex_int : Hexadecimal.signed_int -> int option

  val of_num_int : signed_int -> int option

  val to_uint : int -> Decimal.uint

  val to_hex_uint : int -> Hexadecimal.uint

  val to_num_uint : int -> uint

  val to_num_hex_uint : int -> uint

  val to_int : int -> Decimal.signed_int

  val to_hex_int : int -> Hexadecimal.signed_int

  val to_num_int : int -> signed_int

  val to_num_hex_int : int -> signed_int

  val eq_dec : int -> int -> bool

  val discr : int -> int option

  val binary_rect :
    'a1 -> (int -> 'a1 -> 'a1) -> (int -> 'a1 -> 'a1) -> int -> 'a1

  val binary_rec :
    'a1 -> (int -> 'a1 -> 'a1) -> (int -> 'a1 -> 'a1) -> int -> 'a1

  val peano_rect : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1

  val peano_rec : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1

  val recursion : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1

  val leb_spec0 : int -> int -> reflect

  val ltb_spec0 : int -> int -> reflect

  module Private_OrderTac :
   sig
    module IsTotal :
     sig
     end

    module Tac :
     sig
     end
   end

  val measure_right_induction :
    ('a1 -> int) -> int -> ('a1 -> __ -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 ->
    'a2

  val measure_left_induction :
    ('a1 -> int) -> int -> ('a1 -> __ -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 ->
    'a2

  val measure_induction :
    ('a1 -> int) -> ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2

  module Private_Tac :
   sig
   end

  module Private_Dec :
   sig
    val max_case_strong :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1

    val max_case :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val max_dec : int -> int -> bool

    val min_case_strong :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1

    val min_case :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val min_dec : int -> int -> bool
   end

  val max_case_strong : int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val max_case : int -> int -> 'a1 -> 'a1 -> 'a1

  val max_dec : int -> int -> bool

  val min_case_strong : int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val min_case : int -> int -> 'a1 -> 'a1 -> 'a1

  val min_dec : int -> int -> bool

  module Private_NZPow :
   sig
   end

  module Private_NZSqrt :
   sig
   end

  val sqrt_up : int -> int

  val log2_up : int -> int

  module Private_NZGcdProp :
   sig
   end

  module Private_NDivProp :
   sig
    module Private_NZDiv :
     sig
     end
   end

  module Div0 :
   sig
   end

  module Private_NLcmProp :
   sig
    val lcm : int -> int -> int
   end

  val lcm : int -> int -> int

  module Lcm0 :
   sig
   end

  val eqb_spec : int -> int -> reflect

  val b2n : bool -> int

  val setbit : int -> int -> int

  val clearbit : int -> int -> int

  val ones : int -> int

  val lnot : int -> int -> int
 end
