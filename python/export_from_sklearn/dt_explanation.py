# import sklearn
from sklearn import tree
import os
import subprocess

from export_sklearn_data.export_tree import export_tree
from export_sklearn_data.export_vector import export_vector
from export_sklearn_data.export_features import export_features
from utils import write_str_in_file


def log(text: str, verbose: bool = True):
    if verbose: print(text)

def explain(features: str, dt: tree.DecisionTreeClassifier, v: list, filename: str ="output.txt", verbose: bool = False):
    """
    Explain a decision by calling OCaml program.
    """

    ## write the features, the tree and the vector in a file
    log("begin export...", verbose)
    text_features = export_features(v)
    text_tree = export_tree(dt)
    text_vector = export_vector(v)
    text = text_features + "\n\n" + text_tree + "\n\n" + text_vector + "\n\n"
    write_str_in_file(filename, text)
    log("end export.\n", verbose)

    
    ## compile ocaml code
    log("begin import in ocaml...", verbose)

    verification_prog_path = "../../ocaml/_build/default/bin"

    _commands = f"""
    CURRENT_PROG_PATH=$(pwd)
    cd {verification_prog_path}
    dune build
    dune exec rfxp $CURRENT_PROG_PATH/{filename}
    """
    commands = f"""./{verification_prog_path}/main.exe {filename}"""

    res = subprocess.run(commands, capture_output=True, shell=True, executable="/bin/bash")
    res_str = str(res.stdout, "utf-8")
    print("output :", res_str)
    


    log("end import in ocaml.", verbose)

