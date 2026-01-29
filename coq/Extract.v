Require Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt ExtrOCamlFloats ExtrOcamlNativeString.
Require List.

From RFXP Require Import Utils Features Xp DT RF.

Set Extraction Output Directory "../ocaml/lib/extracted".

Extraction Blacklist List String.

Extraction Language OCaml.
Separate Extraction
    StringOT to_nat to_fin'
    boolean_feature float_feature string_enum_feature enum_feature
    DummyExplainer MakeDT MakeRF.