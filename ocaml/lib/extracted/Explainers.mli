open Datatypes
open Utils
open Xp

module ExplainersDefs :
 functor (E:InputProblem) ->
 sig
  type coq_Xp =
  | Coq_isAXp of E.S.t
  | Coq_isCXp of E.S.t
 end

module AXpIterativeFinder :
 functor (E:InputProblem) ->
 functor (Chk:sig
  module Xp :
   sig
    type coq_Xp =
    | Coq_isAXp of E.S.t
    | Coq_isCXp of E.S.t
   end

  val checkWCXp : E.S.t -> bool
 end) ->
 sig
  module Xp :
   sig
    type coq_Xp =
    | Coq_isAXp of E.S.t
    | Coq_isCXp of E.S.t
   end

  val findAXp : E.S.t -> E.S.t
 end

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
