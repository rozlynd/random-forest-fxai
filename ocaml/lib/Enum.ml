open Datatypes
open MSetInterface
open MSetList
open Orders
open String0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module StringDSO =
 struct
  type t = string

  type eq = __

  type lt = __

  (** val compare : string -> string -> comparison **)

  let compare =
    compare

  (** val eq_equiv : __ **)

  let eq_equiv =
    __

  (** val lt_compat : __ **)

  let lt_compat =
    __

  (** val lt_strorder : __ **)

  let lt_strorder =
    __

  (** val compare_spec : __ **)

  let compare_spec =
    __
 end

module StringOT = DSO_to_OT(StringDSO)

module StringSet = Make(StringOT)
