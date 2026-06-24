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

let help_string = 
  "The program must be called like this :\n
  rfxp filename     -- to just have the result of the explanation
  rfxp -v filename  -- to have informations about the process.
";;

let logger (verbose:bool) (s:string) =
  if verbose then print_string s
;;

(* let main_parsing () =
  let filename = "test_input_file.txt" in
  let fs, t, v = Import.Parse_file.read_file filename in
  Import.Parsing_utils.print_features fs;
  Import.Parsing_utils.print_tree t;
  Import.Parsing_utils.print_vector v
;; *)



let main_file _filename verbose =
  let log = logger verbose in

  (* let _filename = "filename.txt" in *)
  let module D = Driver_file.MakeData (struct
    let filename = _filename
  end) in

  log "debug : défintion du module Input...";
  let module Input = MakeDTInputProblem (D) in
  log "done.\n\n";


  (* log "debug : affichage du vecteur :\n";
  Printing_things.print_vector Input.v;
  log "debug : fin affichage du vecteur.\n\n";

  log "debug : affichage de l'arbre :\n";
  Printing_things.print_tree Input.k Input.fs;
  log "debug : fin affichage de l'arbre.\n\n"; *)


  log "debug : défintion du module Find..." ;
  let module Find = DtAXpFinder (Input) in
  log "done.\n";

  log "debug : recherche...";
  let axp = Find.findAXp Input.S.all in
  log "done.\n";

  log "debug : transformation en liste...";
  let out = string_of_int_list (as_list (module Input.S) axp) in
  log "done.\n";

  log "\nresult :\n\n";
  print_endline out;
  log "\nmain executed.\n\n";
;;


let () =
  if Array.length Sys.argv = 2 then
  main_file Sys.argv.(1) false
  else if Array.length Sys.argv = 3 && Sys.argv.(1) = "-v" then
    main_file Sys.argv.(2) true
  else
    failwith ("Error in calling the program.\n" ^ help_string)



