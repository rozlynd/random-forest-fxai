# Formally Certified Random Forest Explainer

This is a certified program producing explanations for the decisions of an AI using the Random Forest model.  Our definition of a correct explanation follows the work of Joao Marques-Silva around abductive and contrastive explanations—see [On Explaining Random Forests with SAT](https://arxiv.org/abs/2105.10278) and [Logic-Based Explainability: Past, Present & Future](https://arxiv.org/abs/2406.11873).  The algorithm is defined and proved correct in the Coq proof assistant, and then extracted to OCaml.

This is a work in progress.  Currently the extracted program evaluates a random forest defined in `ocaml/lib/Driver.ml`.

### Compilation

The project has been tested with Coq 8.20 and Dune 3.19.  The Dune project is set up in the subdirectory `ocaml/`.  You can run the commands `dune build` and `dune exec rfxp` from that subdirectory.

You will likely have to link the Dune project with Coq's kernel, as the extraction to OCaml's primitive `float` type requires it.  Look for the directory `coq-core/` in your installation and check that it contains a `dune` or `dune-package` file.  The easiest way to link this to the project is to set up a symbolic link:
```bash
ln -s -T ~/.opam/myswitch/lib/coq-core ocaml/coq-core
```
You may need to edit the name of the dependency in `ocaml/lib/dune` from `coq-core.kernel` to the library name that is used in the Dune file in `coq-core/`.

The OCaml files extracted from the Coq sources are already present in the Dune project.  If you wish to extract the files again, you can run the `make` command from the `coq/` subdirectory.
