open Datatypes
open Xp

module ExplainersDefs =
 functor (E:InputProblem) ->
 struct
  type coq_Xp =
  | Coq_isAXp of E.S.t
  | Coq_isCXp of E.S.t
 end

module AXpIterativeFinder =
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
 struct
  module Xp = ExplainersDefs(E)

  (** val checkWAXp : E.S.t -> bool **)

  let checkWAXp x =
    negb (Chk.checkWCXp (E.S.compl x))

  (** val findAXp : E.S.t -> E.S.t **)

  let findAXp =
    E.S.shrink checkWAXp
 end

module DummyExplainer =
 functor (E:InputProblem) ->
 struct
  module Xp = ExplainersDefs(E)

  (** val getNew : Xp.coq_Xp list -> Xp.coq_Xp option **)

  let getNew _ =
    Some (Xp.Coq_isAXp E.S.all)
 end
