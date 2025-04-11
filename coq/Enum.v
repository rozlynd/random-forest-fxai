Require Import String Orders MSets.

Module StringOT : UsualOrderedType with Definition t := string :=
    String_as_OT.

Module StringOTF : UsualOrderedTypeFull with Definition t := string :=
    OT_to_Full StringOT.

Module StringSet : Sets with Module E := StringOT :=
    MSetList.Make StringOT.

Module StringSetProperties := OrdProperties StringSet.
Export StringSetProperties.P.


Section EnumDefinition.

    Import StringSet.

    Definition enum (s : StringSet.t) := { x : string | In x s }.

End EnumDefinition.