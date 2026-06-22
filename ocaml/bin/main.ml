open Rfxp
open Driver_file
(* open Driver *)
open Extracted
(* open Import *)
open DTXp
(* open DT *)
open Utils
(* open Printing_things *)



let as_list (type t_) (module S : FinSet with type t = t_) (e : S.t) =
  let l = S.elements e in
  List.map (fun f -> Extracted.Utils.to_nat S.n f + 1) l
;;




let string_of_int_list l =
  let rec aux acc l =
    match l with
    | [] -> acc ^ " ]"
    | x :: l -> aux (acc ^ ", " ^ string_of_int x) l
  in
  match l with
  | [] -> "[]"
  | x :: l -> aux ("[ " ^ string_of_int x) l
;;


let main_parsing () =
  let filename = "test_input_file.txt" in
  let fs, t, v = Import.Parse_file.read_file filename in
  Import.Parsing_utils.print_features fs;
  Import.Parsing_utils.print_tree t;
  Import.Parsing_utils.print_vector v
;;



let main_file _filename =
  (* let _filename = "filename.txt" in *)
  let module D = Driver_file.MakeData (struct
    let filename = _filename
  end) in

  print_string "debug : défintion du module Input...";
  let module Input = MakeDTInputProblem (D) in
  print_endline "done.\n";


  print_endline "debug : affichage du vecteur :";
  Printing_things.print_vector Input.v;
  print_endline "debug : fin affichage du vecteur.\n";

  print_endline "debug : affichage de l'arbre :";
  Printing_things.print_tree Input.k Input.fs;
  print_endline "debug : fin affichage de l'arbre.\n";


  print_string "debug : défintion du module Find..." ;
  let module Find = DtAXpFinder (Input) in
  print_endline "done.";

  print_string "debug : recherche...";
  let axp = Find.findAXp Input.S.all in
  print_endline "done.";

  print_string "debug : transformation en liste...";
  let out = string_of_int_list (as_list (module Input.S) axp) in
  print_endline "done.";

  print_endline "\nresult :";
  print_endline out;
  print_endline "\nmain executed.";
;;


let () =
  if Array.length Sys.argv > 1 then
    main_file Sys.argv.(1)
  else
    main_parsing ()



