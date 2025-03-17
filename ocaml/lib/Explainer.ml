open DT
open InputData

(** val print_class : coq_class -> unit **)

let print_class = Driver.print_class

(** val read_input : unit -> input_data **)

let read_input = Driver.read_input

(** val main : unit -> unit **)

let main _ =
  let input = read_input () in
  let fs = input.features in
  let dt = input.decision_tree in
  let x = input.instance in
  let c = evalDT input.n_features fs dt x in print_class c
