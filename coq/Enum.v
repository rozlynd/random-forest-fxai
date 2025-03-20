Require Import String Orders MSets.

Module StringOT : OrderedType with Definition t := string :=
    String_as_OT.

Module StringSet : Sets with Module E := StringOT :=
    MSetList.Make StringOT.

Module StringSetProperties := OrdProperties StringSet.
Export StringSetProperties.P.


Section EnumDefinition.

    Import StringSet.

    Definition enum (s : StringSet.t) := { x : string | In x s }.

End EnumDefinition.