open Bool
open Equalities
open Explainers
open Features
open Utils
open Xp

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module type DTInputProblem =
 sig
  val n : int

  val fs : featureSig

  module K :
   UsualDecidableType

  type t = K.t DT.dt

  val eval : t -> featureVec -> K.t

  val k : t

  val v : featureVec

  module S :
   FinSet
 end

module DtWCXpCheckerImpl =
 functor (C:DT.DT) ->
 functor (S:FinSet) ->
 struct
  module FD = FeatureSigDefs(C)(S)

  type coq_constraint (* AXIOM TO BE REALIZED *)

  (** val update : fin -> testIndex -> coq_constraint -> coq_constraint **)

  let update =
    failwith "AXIOM TO BE REALIZED (RFXP.DTXp.DtWCXpCheckerImpl.update)"

  (** val nupdate : fin -> testIndex -> coq_constraint -> coq_constraint **)

  let nupdate =
    failwith "AXIOM TO BE REALIZED (RFXP.DTXp.DtWCXpCheckerImpl.nupdate)"

  (** val witness : coq_constraint -> featureVec option **)

  let witness =
    failwith "AXIOM TO BE REALIZED (RFXP.DTXp.DtWCXpCheckerImpl.witness)"

  (** val refute_aux :
      featureVec -> C.K.t -> S.t -> coq_constraint -> C.t -> featureVec option **)

  let rec refute_aux v0 c0 x c = function
  | DT.Leaf c1 -> if C.K.eq_dec c1 c0 then None else witness c
  | DT.Node (i, test, dt1, dt2) ->
    if S.mem i x
    then (match refute_aux v0 c0 x (update i test c) dt1 with
          | Some r -> Some r
          | None -> refute_aux v0 c0 x (nupdate i test c) dt2)
    else let dt' = if featureTest' C.n C.fs v0 i test then dt1 else dt2 in
         refute_aux v0 c0 x c dt'

  (** val init : S.t -> coq_constraint **)

  let init =
    failwith "AXIOM TO BE REALIZED (RFXP.DTXp.DtWCXpCheckerImpl.init)"

  (** val refute : C.t -> featureVec -> S.t -> featureVec option **)

  let refute dt0 v0 x =
    refute_aux v0 (C.eval dt0 v0) x (init x) dt0
 end

module DtWCXpChecker =
 functor (E_:DTInputProblem) ->
 struct
  module E = E_

  module Xp = ExplainersDefs(E)

  module Impl = DtWCXpCheckerImpl(E)(E.S)

  (** val checkWCXp : E_.S.t -> bool **)

  let checkWCXp x =
    match Impl.refute E.k E.v x with
    | Some _ -> false
    | None -> true

  (** val checkWCXpSound : E.S.t -> reflect **)

  let checkWCXpSound =
    failwith "AXIOM TO BE REALIZED (RFXP.DTXp.DtWCXpChecker.checkWCXpSound)"
 end

module DtAXpFinder =
 functor (E_:DTInputProblem) ->
 struct
  module Chk = DtWCXpChecker(E_)

  module Impl = AXpIterativeFinder(E_)(Chk)

  module E = E_

  module Xp = Impl.Xp

  (** val findAXp : E.S.t -> E.S.t **)

  let findAXp =
    Impl.findAXp

  (** val findAXpSound : __ **)

  let findAXpSound =
    __

  (** val findAXpSane : __ **)

  let findAXpSane =
    __
 end

module DtCXpFinder =
 functor (E_:DTInputProblem) ->
 struct
  module Chk = DtWCXpChecker(E_)

  module Impl = CXpIterativeFinder(E_)(Chk)

  module E = E_

  module Xp = Impl.Xp

  (** val findCXp : E.S.t -> E.S.t **)

  let findCXp =
    Impl.findCXp

  (** val findCXpSound : __ **)

  let findCXpSound =
    __

  (** val findCXpSane : __ **)

  let findCXpSane =
    __
 end
