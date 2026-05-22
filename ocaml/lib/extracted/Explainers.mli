open Bool
open Equalities
open Features
open Utils
open Xp

type __ = Obj.t

module ExplainersDefs :
 functor (E:InputProblem) ->
 sig
 end

module EnumeratorsDefs :
 functor (E:InputProblem) ->
 sig
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

module AXpIterativeFinder :
 functor (E_:InputProblem) ->
 functor (Chk:WCXpChecker with module E = E_) ->
 AXpFinder with module E = E_

module CXpIterativeFinder :
 functor (E_:InputProblem) ->
 functor (Chk:WCXpChecker with module E = E_) ->
 CXpFinder with module E = E_

module DummyExplainer :
 functor (E:InputProblem) ->
 sig
  module Xp :
   sig
    type coq_Xp =
    | Coq_isAXp of E.S.t
    | Coq_isCXp of E.S.t
   end

  val getNew : Xp.coq_Xp list -> Xp.coq_Xp option
 end
