Require Import List Orders.
Require OrdersEx.
Import ListNotations.

(* Implementation of a voting function that computes the element with the
   most occurrences in a list.  A decidable order must be provided to
   select the minimum element if there are several candidates. *)

(* OrderedType restricted to Usual because count_occ needs the usual
   equality to be decidable *)
Module Type VotingSig (OT : UsualOrderedType).

    Module OTF : UsualOrderedTypeFull
        with Definition t := OT.t := OT_to_Full OT.
    Import OTF.

    Parameter vote : t -> list t -> t.

    Local Definition count_occ := count_occ eq_dec.

    Axiom vote_In : forall (x : t) (l : list t),
        In (vote x l) (x :: l).

    Axiom vote_count_le : forall (x : t) (l : list t) (y : t),
        count_occ (x :: l) y <= count_occ (x :: l) (vote x l).

    Axiom vote_count_max : forall (x : t) (l : list t) (y : t),
        In y l ->
        count_occ (x :: l) y = count_occ (x :: l) (vote x l) ->
        le (vote x l) y.

End VotingSig.
