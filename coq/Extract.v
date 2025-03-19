Require Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt ExtrOCamlFloats ExtrOcamlNativeString.
Require List.

From RFXP Require Import Features Explainer.

Set Extraction Output Directory "../ocaml/lib".

Extraction Blacklist List String.

Extraction Language OCaml.
Separate Extraction Main boolean_feature int_feature float_feature enum_feature.