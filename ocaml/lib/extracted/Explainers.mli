open Xp

module ExplainersDefs :
 functor (E:InputProblem) ->
 sig
  type coq_Xp =
  | Coq_isAXp of E.S.t
  | Coq_isCXp of E.S.t
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
