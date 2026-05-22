open Bool
open Datatypes
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

module AXpIterativeFinderBase =
 functor (E:InputProblem) ->
 functor (Chk:sig
  module Xp :
   sig
   end

  val checkWCXp : E.S.t -> bool

  val checkWCXpSound : E.S.t -> reflect
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

module AXpIterativeFinder =
 functor (E:InputProblem) ->
 functor (Chk:sig
  module Xp :
   sig
   end

  val checkWCXp : E.S.t -> bool

  val checkWCXpSound : E.S.t -> reflect
 end) ->
 struct
  module Impl = AXpIterativeFinderBase(E)(Chk)

  module Xp = Impl.Xp

  (** val checkWAXp : E.S.t -> bool **)

  let checkWAXp x =
    negb (Chk.checkWCXp (E.S.compl x))

  (** val findAXp : E.S.t -> E.S.t **)

  let findAXp =
    E.S.shrink checkWAXp

  (** val findAXpSound : __ **)

  let findAXpSound =
    __

  (** val findAXpSane : __ **)

  let findAXpSane =
    __
 end

module CXpIterativeFinderBase =
 functor (E:InputProblem) ->
 functor (Chk:sig
  module Xp :
   sig
   end

  val checkWCXp : E.S.t -> bool

  val checkWCXpSound : E.S.t -> reflect
 end) ->
 struct
  module Xp = ExplainersDefs(E)

  (** val findCXp : E.S.t -> E.S.t **)

  let findCXp =
    E.S.shrink Chk.checkWCXp
 end

module CXpIterativeFinder =
 functor (E:InputProblem) ->
 functor (Chk:sig
  module Xp :
   sig
   end

  val checkWCXp : E.S.t -> bool

  val checkWCXpSound : E.S.t -> reflect
 end) ->
 struct
  module Impl = CXpIterativeFinderBase(E)(Chk)

  module Xp = Impl.Xp

  (** val findCXp : E.S.t -> E.S.t **)

  let findCXp =
    E.S.shrink Chk.checkWCXp

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
