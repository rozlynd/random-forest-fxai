open Basics
open Datatypes
open Equalities
open Features
open List0
open Utils

type __ = Obj.t

module type FeatureSig =
 sig
  val n : int

  val fs : featureSig
 end

module type Output =
 sig
  module K :
   UsualDecidableType
 end

module type ExplanationProblem =
 sig
  val n : int

  val fs : featureSig

  module K :
   UsualDecidableType

  type t

  val eval : t -> featureVec -> K.t

  val k : t

  val v : featureVec
 end

module ExplanationsDefs :
 functor (E__7:ExplanationProblem) ->
 sig
  module S :
   sig
    module X :
     sig
      type t = fin

      val compare : t -> t -> comparison

      val eq_dec : t -> t -> bool
     end

    module Raw :
     sig
      module MX :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = fin

            val compare : fin -> fin -> comparison

            val eq_dec : fin -> fin -> bool
           end

          module TO :
           sig
            type t = fin

            val compare : fin -> fin -> comparison

            val eq_dec : fin -> fin -> bool
           end
         end

        val eq_dec : fin -> fin -> bool

        val lt_dec : fin -> fin -> bool

        val eqb : fin -> fin -> bool
       end

      module ML :
       sig
       end

      type elt = fin

      type t = elt list

      val empty : t

      val is_empty : t -> bool

      val mem : fin -> fin list -> bool

      val add : fin -> fin list -> fin list

      val singleton : elt -> elt list

      val remove : fin -> fin list -> t

      val union : t -> t -> t

      val inter : t -> t -> t

      val diff : t -> t -> t

      val equal : t -> t -> bool

      val subset : fin list -> fin list -> bool

      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

      val filter : (elt -> bool) -> t -> t

      val for_all : (elt -> bool) -> t -> bool

      val exists_ : (elt -> bool) -> t -> bool

      val partition : (elt -> bool) -> t -> t * t

      val cardinal : t -> int

      val elements : t -> elt list

      val min_elt : t -> elt option

      val max_elt : t -> elt option

      val choose : t -> elt option

      val compare : fin list -> fin list -> comparison

      val inf : fin -> fin list -> bool

      val isok : fin list -> bool

      module L :
       sig
        module MO :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = fin

              val compare : fin -> fin -> comparison

              val eq_dec : fin -> fin -> bool
             end

            module TO :
             sig
              type t = fin

              val compare : fin -> fin -> comparison

              val eq_dec : fin -> fin -> bool
             end
           end

          val eq_dec : fin -> fin -> bool

          val lt_dec : fin -> fin -> bool

          val eqb : fin -> fin -> bool
         end
       end
     end

    module E :
     sig
      type t = fin

      val compare : fin -> fin -> comparison

      val eq_dec : fin -> fin -> bool
     end

    type elt = fin

    type t_ = Raw.t
      (* singleton inductive, whose constructor was Mkt *)

    val this : t_ -> Raw.t

    type t = t_

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val remove : elt -> t -> t

    val singleton : elt -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : t -> t -> bool

    val empty : t

    val is_empty : t -> bool

    val elements : t -> elt list

    val choose : t -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val cardinal : t -> int

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> t * t

    val eq_dec : t -> t -> bool

    val compare : t -> t -> comparison

    val min_elt : t -> elt option

    val max_elt : t -> elt option

    val all_below : int -> t option

    val all_obligation_1 : __ -> t

    val all : t

    val compl : t -> t
   end

  type coq_Xp =
  | Coq_isAXp of S.t
  | Coq_isCXp of S.t
 end

module DummyExplainer :
 functor (E:ExplanationProblem) ->
 sig
  module Xp :
   sig
    module S :
     sig
      module X :
       sig
        type t = fin

        val compare : t -> t -> comparison

        val eq_dec : t -> t -> bool
       end

      module Raw :
       sig
        module MX :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = fin

              val compare : fin -> fin -> comparison

              val eq_dec : fin -> fin -> bool
             end

            module TO :
             sig
              type t = fin

              val compare : fin -> fin -> comparison

              val eq_dec : fin -> fin -> bool
             end
           end

          val eq_dec : fin -> fin -> bool

          val lt_dec : fin -> fin -> bool

          val eqb : fin -> fin -> bool
         end

        module ML :
         sig
         end

        type elt = fin

        type t = elt list

        val empty : t

        val is_empty : t -> bool

        val mem : fin -> fin list -> bool

        val add : fin -> fin list -> fin list

        val singleton : elt -> elt list

        val remove : fin -> fin list -> t

        val union : t -> t -> t

        val inter : t -> t -> t

        val diff : t -> t -> t

        val equal : t -> t -> bool

        val subset : fin list -> fin list -> bool

        val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

        val filter : (elt -> bool) -> t -> t

        val for_all : (elt -> bool) -> t -> bool

        val exists_ : (elt -> bool) -> t -> bool

        val partition : (elt -> bool) -> t -> t * t

        val cardinal : t -> int

        val elements : t -> elt list

        val min_elt : t -> elt option

        val max_elt : t -> elt option

        val choose : t -> elt option

        val compare : fin list -> fin list -> comparison

        val inf : fin -> fin list -> bool

        val isok : fin list -> bool

        module L :
         sig
          module MO :
           sig
            module OrderTac :
             sig
              module OTF :
               sig
                type t = fin

                val compare : fin -> fin -> comparison

                val eq_dec : fin -> fin -> bool
               end

              module TO :
               sig
                type t = fin

                val compare : fin -> fin -> comparison

                val eq_dec : fin -> fin -> bool
               end
             end

            val eq_dec : fin -> fin -> bool

            val lt_dec : fin -> fin -> bool

            val eqb : fin -> fin -> bool
           end
         end
       end

      module E :
       sig
        type t = fin

        val compare : fin -> fin -> comparison

        val eq_dec : fin -> fin -> bool
       end

      type elt = fin

      type t_ = Raw.t
        (* singleton inductive, whose constructor was Mkt *)

      val this : t_ -> Raw.t

      type t = t_

      val mem : elt -> t -> bool

      val add : elt -> t -> t

      val remove : elt -> t -> t

      val singleton : elt -> t

      val union : t -> t -> t

      val inter : t -> t -> t

      val diff : t -> t -> t

      val equal : t -> t -> bool

      val subset : t -> t -> bool

      val empty : t

      val is_empty : t -> bool

      val elements : t -> elt list

      val choose : t -> elt option

      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

      val cardinal : t -> int

      val filter : (elt -> bool) -> t -> t

      val for_all : (elt -> bool) -> t -> bool

      val exists_ : (elt -> bool) -> t -> bool

      val partition : (elt -> bool) -> t -> t * t

      val eq_dec : t -> t -> bool

      val compare : t -> t -> comparison

      val min_elt : t -> elt option

      val max_elt : t -> elt option

      val all_below : int -> t option

      val all_obligation_1 : __ -> t

      val all : t

      val compl : t -> t
     end

    type coq_Xp =
    | Coq_isAXp of S.t
    | Coq_isCXp of S.t
   end

  val getNew : Xp.coq_Xp list -> Xp.coq_Xp
 end
