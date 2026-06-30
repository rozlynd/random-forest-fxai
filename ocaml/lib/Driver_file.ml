open Dttxt

open Parse_file
open Parsing_utils


open Extracted

open Utils
open Features
open Xp
open Explainers
open DT
open DTXp

open Convert_data




let set_of_string_list l =
  List.fold_right StringSet.add l StringSet.empty

let s = set_of_string_list [ "s1" ; "s2" ; "s3" ]

(* module F : FeatureSig = struct

  let n = 3

  let fs =
    Coq_featureSigCons (2, float_feature, Coq_isContinuousFeature,
    Coq_featureSigCons (1, boolean_feature, Coq_isBooleanFeature,
    Coq_featureSigCons (0, string_enum_feature s, Coq_isStringEnumFeature s,
    Coq_featureSigNil)))

end *)

(* module O : Output with module K = StringOT = struct

  module K = StringOT

end *)

(* module Dt = MakeDT (F) (O) *)

module type Data = sig
  val nb_features : int
  val features : parsed_features
  val parsed_tree : parsed_tree
  val parsed_vector : parsed_vector
end

module type FileNameModule = sig
  val filename : string
end

module MakeData = functor (F:FileNameModule) -> struct
  let fs, t, v = Parse_file.read_file F.filename
  let nb_features = List.length fs
  let features = fs
  let parsed_tree = t
  let parsed_vector = v
end



module MakeDTInputProblem (Data:Data) : DTInputProblem with module K = StringOT =
 
 struct

  let v_, fs_ = vector_and_features_from_parsing Data.parsed_vector Data.features
  
  module F : FeatureSig = struct
    let n = Data.nb_features
    let fs = fs_
  end

  module O : Output with module K = StringOT = struct
    module K = StringOT
  end

  module Dt = MakeDT (F) (O)
  
  let n = F.n

  let fs = F.fs

  module K = O.K

  type t = Dt.t

  let eval = Dt.eval

  let to_fin = to_fin' n

  let k = tree_from_parsing to_fin Data.parsed_tree
  (* let _ = print_string "debug : affichage de l'arbre..."
  let _  = Printing_things.print_tree k fs
  let _ = print_endline "done." *)

  let v = v_

  module S = MakeFinSet (struct let n = n end)
end

