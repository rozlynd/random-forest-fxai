Require Import String Orders MSets.

Module StringDSO : DecStrOrder with Definition t := string.

    Definition t := string.
    Definition eq (s t : string) := s = t.
    Definition lt (s t : string) := compare s t = Lt.
    Definition compare (s t : string) := compare s t.

    Instance eq_equiv : Equivalence eq := eq_equivalence.

    Program Instance lt_compat : Proper (eq ==> eq ==> iff) lt := {}.
    Next Obligation.
        intros s t Heq s' t' Heq'.
        rewrite Heq, Heq'.
        apply iff_refl.
    Qed.

    Program Instance lt_strorder : StrictOrder lt.

    Lemma compare_spec (s t : string) : CompSpec eq lt s t (compare s t).
    Proof.
        unfold compare.
        destruct (s ?= t)%string eqn:Heq; constructor.
        apply compare_eq_iff, Heq.
        apply Heq.
        unfold lt. rewrite compare_antisym.
        unfold CompOpp. now rewrite Heq.
    Qed.

End StringDSO.

Module StringOT : OrderedType with Definition t := string :=
    DSO_to_OT StringDSO.

Module StringSet : Sets with Module E := StringOT :=
    MSetList.Make StringOT.

Module StringSetProperties := OrdProperties StringSet.
Export StringSetProperties.P.


Section EnumDefinition.

    Import StringSet.

    Definition enum (s : StringSet.t) := { x : string | In x s }.

End EnumDefinition.