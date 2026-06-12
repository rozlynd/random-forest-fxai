open Rfxp
open Driver

let as_list (e : Input.S.t) : int list =
  let l = Input.S.elements e in
  List.map (fun f -> Extracted.Utils.to_nat Input.S.n f + 1) l

let string_of_int_list l =
  let rec aux acc l =
    match l with
    | [] -> acc ^ " ]"
    | x :: l -> aux (acc ^ ", " ^ string_of_int x) l
  in
  match l with
  | [] -> "[]"
  | x :: l -> aux ("[ " ^ string_of_int x) l

let () =
  let axp = AXpFind.findAXp Input.S.all in
  let out = string_of_int_list (as_list axp) in
  print_endline out
