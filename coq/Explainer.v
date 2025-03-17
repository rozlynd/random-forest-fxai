Require Extraction.
From RFXP Require Import Features DT RF CNF Sat InputData.

Parameter print_class : class -> unit.
Extract Constant print_class => "Driver.print_class".

Parameter read_input : unit -> input_data.
Extract Constant read_input => "Driver.read_input".

Definition main (_ : unit) : unit :=
    let input := read_input tt in
    let fs := features input in
    let dt := decision_tree input in
    let x := instance input in
    let c : class := DT.evalDT class fs dt x in
    print_class c.