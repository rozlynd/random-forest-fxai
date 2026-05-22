open Bool
open Equalities
open Features
open Utils
open Xp

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module ExplainersDefs =
 functor (E:InputProblem) ->
 struct
 end

module EnumeratorsDefs =
 functor (E:InputProblem) ->
 struct
  type coq_Xp =
  | Coq_isAXp of E.S.t
  | Coq_isCXp of E.S.t
 end

module type AXpFinder =
 sig
  module E :
   InputProblem

  module Xp :
   sig
   end

  val findAXp : E.S.t -> E.S.t
 end

module type CXpFinder =
 sig
  module E :
   InputProblem

  module Xp :
   sig
   end

  val findCXp : E.S.t -> E.S.t
 end

module type WCXpChecker =
 sig
  module E :
   InputProblem

  module Xp :
   sig
   end

  val checkWCXp : E.S.t -> bool

  val checkWCXpSound : E.S.t -> reflect
 end

module AXpIterativeFinder =
 functor (E_:InputProblem) ->
 functor (Chk:WCXpChecker with module E = E_) ->
 struct
  module E = E_

  module Xp = ExplainersDefs(E_)

  (** val findAXp : E_.S.t -> E_.S.t **)

  let findAXp =
    failwith "AXIOM TO BE REALIZED (RFXP.Explainers.AXpIterativeFinder.findAXp)"

  (** val findAXpSound : __ **)

  let findAXpSound =
    __

  (** val findAXpSane : __ **)

  let findAXpSane =
    __
 end

module CXpIterativeFinder =
 functor (E_:InputProblem) ->
 functor (Chk:WCXpChecker with module E = E_) ->
 struct
  module E = E_

  module Xp = ExplainersDefs(E_)

  (** val findCXp : E_.S.t -> E_.S.t **)

  let findCXp =
    failwith "AXIOM TO BE REALIZED (RFXP.Explainers.CXpIterativeFinder.findCXp)"

  (** val findCXpSound : __ **)

  let findCXpSound =
    __

  (** val findCXpSane : __ **)

  let findCXpSane =
    __
 end

module DummyExplainer =
 functor (E:InputProblem) ->
 struct
  module Xp = EnumeratorsDefs(E)

  (** val getNew : Xp.coq_Xp list -> Xp.coq_Xp option **)

  let getNew _ =
    Some (Xp.Coq_isAXp E.S.all)
 end
