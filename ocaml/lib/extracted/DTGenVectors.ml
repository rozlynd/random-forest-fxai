open DTXp
open Equalities
open Features

module type DTInstance =
 sig
  val n : int

  val fs : featureSig

  module K :
   UsualDecidableType

  type t = K.t DT.dt

  val eval : t -> featureVec -> K.t

  val k : t
 end

(** val initConstraintFull : int -> featureSig -> featureSpaceConstraint **)

let rec initConstraintFull _ = function
| Coq_featureSigNil -> Coq_featureSpaceConstraintNil
| Coq_featureSigCons (n0, f, fs1) ->
  Coq_featureSpaceConstraintCons (f, (constraintInitFull f), n0, fs1,
    (initConstraintFull n0 fs1))

module DtGenVectors =
 functor (Dt:DTInstance) ->
 struct
  (** val gen_aux :
      featureSpaceConstraint -> Dt.t -> featureVec list -> featureVec list **)

  let rec gen_aux c dt0 acc =
    match dt0 with
    | DT.Leaf _ ->
      (match witness Dt.n Dt.fs c with
       | Some v -> v :: acc
       | None -> acc)
    | DT.Node (i, test, dt1, dt2) ->
      let cleft = splitLeft Dt.n Dt.fs i test c in
      let cRight = splitRight Dt.n Dt.fs i test c in
      let acc0 = gen_aux cleft dt1 acc in gen_aux cRight dt2 acc0

  (** val gen : unit -> featureVec list **)

  let gen _ =
    gen_aux (initConstraintFull Dt.n Dt.fs) Dt.k []
 end
