
type 'a coq_sig = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| Coq_existT of 'a * 'p

type ('a, 'p, 'q) sigT2 =
| Coq_existT2 of 'a * 'p * 'q

val projT1 : ('a1, 'a2) sigT -> 'a1


