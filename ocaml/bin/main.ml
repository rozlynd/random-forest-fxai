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
  "The program must be called like this :                             \n
  rfxp [-v] [ -a | -c | -ac | -all ] <input_file> [<output_file>]     \n
    -v    verbose                                                     \n
    -a    get one AXp                                                 \n
    -c    get one CXp                                                 \n
    -ac   get one AXp and one CXp                                     \n
    -all  get all AXp and all CXp (caution : AXp and CXp are mixed)   \n\n

    <input_file>    the file containing Decision Tree informations.   \n
    <output_file>   the file to write the results."
;;

let logger (verbose:bool) (s:string) =
  if verbose then print_string s
;;



(* enum type giving the research goal. *)
type mode = 
  | AXp
  | CXp
  | Both
  | All
;;

(* write a string message in a file named filename. *)
let write_in_file message filename = 
  let oc = open_out filename in
  Printf.fprintf oc "%s\n" message;
  close_out oc
;;

let main_file verbose mode input_file output_file =
  let log = logger verbose in

  (* let _filename = "filename.txt" in *)
  let module D = Driver_file.MakeData (struct
    let filename = input_file
  end) in

  log "info : parsing file...";
  let module Input = MakeDTInputProblem (D) in
  log "done.\n\n";

  if mode = All then
    failwith "Error : parameter -all is not available yet.";

  if mode = AXp || mode = Both then
    begin
      let module FindA = DtAXpFinder (Input) in
      let axp = FindA.findAXp Input.S.all in
      let outA = string_of_int_list (as_list (module Input.S) axp) in
      print_endline ("AXp : " ^ outA);
    end;
    
  if mode = CXp || mode = Both then
    begin
      let module FindC = DtCXpFinder (Input) in
      let cxp = FindC.findCXp Input.S.all in
      let outC = string_of_int_list (as_list (module Input.S) cxp) in
      print_endline ("CXp : " ^ outC);
    end;
  
  write_in_file "test" output_file;

  log "info : main executed.\n";
;;


let () =
  let verbose = ref false in
  let mode = ref AXp in
  let input_file = ref "data.txt" in
  let input_file_given = ref false in
  let output_file = ref "dt_explanation_result.txt" in
  let output_file_given = ref false in
  for i=1 to (Array.length Sys.argv - 1) do
    let a =  Sys.argv.(i) in
    if a = "-v" then
      verbose := true
    else if a = "-a" then
      mode := AXp
    else if a = "-c" then
      mode := CXp
    else if a = "-ac" then
      mode := Both
    else if a = "-all" then
      mode := All
    else if a.[0] = '-' then
      failwith ("Error : unknown parameter " ^ a)
    else if (not !input_file_given) then
      begin 
        input_file_given := true; 
        input_file := a
      end
    else if (not !output_file_given) then
      begin 
        output_file_given := true; 
        output_file := a
      end
    else
      failwith ("Error in command line arguments.\n" ^ help_string)
  done;
  main_file !verbose !mode !input_file !output_file






















(* let () =
  if Array.length Sys.argv = 2 then
    main_file Sys.argv.(1) false
  else if Array.length Sys.argv = 3 && Sys.argv.(1) = "-v" then
    main_file Sys.argv.(2) true
  else
    failwith ("Error in command line arguments.\n" ^ help_string) *)


(* let main_parsing () =
  let filename = "test_input_file.txt" in
  let fs, t, v = Import.Parse_file.read_file filename in
  Import.Parsing_utils.print_features fs;
  Import.Parsing_utils.print_tree t;
  Import.Parsing_utils.print_vector v
;; *)

(* let main_file _filename verbose =
  let log = logger verbose in

  (* let _filename = "filename.txt" in *)
  let module D = Driver_file.MakeData (struct
    let filename = _filename
  end) in

  log "debug : défintion du module Input...";
  let module Input = MakeDTInputProblem (D) in
  log "done.\n\n";


  log "debug : défintion du module Find..." ;
  let module FindA = DtAXpFinder (Input) in
  let module FindC = DtCXpFinder (Input) in
  log "done.\n";

  log "debug : recherche...";
  let axp = FindA.findAXp Input.S.all in
  let cxp = FindC.findCXp Input.S.all in
  log "done.\n";

  log "debug : transformation en liste...";
  let outA = string_of_int_list (as_list (module Input.S) axp) in
  let outC = string_of_int_list (as_list (module Input.S) cxp) in
  log "done.\n";

  log "\nresult :\n\n";
  print_endline outA;
  print_endline outC;
  log "\nmain executed.\n\n";
;; *)
