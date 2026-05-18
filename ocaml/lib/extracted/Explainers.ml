open Datatypes
open Utils
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

  (** val findAXp_aux : E.S.t -> int -> E.S.t option **)

  let rec findAXp_aux x i =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Some x)
      (fun i0 ->
      let filtered_var = to_fin E.S.n i0 in
      (match filtered_var with
       | Some k ->
         let x' =
           let x' = E.S.remove k x in
           if (&&) (E.S.mem k x) (negb (Chk.checkWCXp (E.S.compl x')))
           then x'
           else x
         in
         let filtered_var0 = findAXp_aux x' i0 in
         (match filtered_var0 with
          | Some r -> Some r
          | None -> None)
       | None -> None))
      i

  (** val findAXp : E.S.t -> E.S.t **)

  let findAXp x =
    let filtered_var = findAXp_aux x E.S.n in
    (match filtered_var with
     | Some r -> r
     | None -> assert false (* absurd case *))
 end

module DummyExplainer =
 functor (E:InputProblem) ->
 struct
  module Xp = ExplainersDefs(E)

  (** val getNew : Xp.coq_Xp list -> Xp.coq_Xp option **)

  let getNew _ =
    Some (Xp.Coq_isAXp E.S.all)
 end
