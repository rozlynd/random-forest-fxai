open Xp

module ExplainersDefs =
 functor (E:InputProblem) ->
 struct
  type coq_Xp =
  | Coq_isAXp of E.S.t
  | Coq_isCXp of E.S.t
 end

module DummyExplainer =
 functor (E:InputProblem) ->
 struct
  module Xp = ExplainersDefs(E)

  (** val getNew : Xp.coq_Xp list -> Xp.coq_Xp option **)

  let getNew _ =
    Some (Xp.Coq_isAXp E.S.all)
 end
