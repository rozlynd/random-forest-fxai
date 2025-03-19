open Rfxp

module Rfxp_main = Explainer.Main(Driver.InputData)

let () = print_endline (Rfxp_main.main ())
