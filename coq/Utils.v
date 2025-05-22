Require Import String Orders MSets.

(* String utils *)

Module StringOT : UsualOrderedType
    with Definition t := string :=
    String_as_OT.

Module StringOTF : UsualOrderedTypeFull
    with Definition t := string :=
    OT_to_Full StringOT.

Module StringSet : Sets
    with Module E := StringOT :=
    MSetList.Make StringOT.

Module StringSetProperties := OrdProperties StringSet.
Export StringSetProperties StringSetProperties.P.


(* Non-empty lists *)

Section NonEmptyList.

    Variable (A : Type).

    Inductive nelist :=
    | necons (x : A) (l : list A).

End NonEmptyList.

Arguments necons {A}.