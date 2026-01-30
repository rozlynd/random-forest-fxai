# Formally Certified Random Forest Explainer

This is a certified program producing explanations for the decisions of an AI using the Random Forest model.  Our definition of a correct explanation follows the work of Joao Marques-Silva around abductive and contrastive explanations—see [On Explaining Random Forests with SAT](https://arxiv.org/abs/2105.10278) and [Logic-Based Explainability: Past, Present & Future](https://arxiv.org/abs/2406.11873).  The algorithm is defined and proved correct in the Coq proof assistant, and then extracted to OCaml.

This is a work in progress.  Currently the extracted program evaluates a random forest defined in `ocaml/lib/Driver.ml`.

### Compilation

The project has been tested with Coq 8.20 and Dune 3.19.  The Dune project is set up in the subdirectory `ocaml/`.  You can run the commands `dune build` and `dune exec rfxp` from that subdirectory.

You may have to link the Dune project with Coq's kernel, as the extraction to OCaml's primitive `float` type requires it.  Look for the directory `coq-core/` in your installation and check that it contains a `dune` or `dune-package` file.  The easiest way to link this to the project is to set up a symbolic link:
```bash
ln -s -T ~/.opam/myswitch/lib/coq-core ocaml/coq-core
```
You may need to edit the name of the dependency in `ocaml/lib/dune` from `coq-core.kernel` to the library name that is used in the Dune file in `coq-core/`.

The OCaml files extracted from the Coq sources are already present in the Dune project.  If you wish to extract the files again, you can run `make coq-extract` from the root directory.

### Using the Extracted Modules

The extracted code can be found in `ocaml/lib/extracted/`. The intended way to use it is to instantiate various OCaml modules in order to derive an explainer. We describe the important modules.

`Features.mli` contains the following important types:
-   `featureSig` for lists of features---the predefined types `boolean_feature`, `float_feature`, `string_enum_feature` and `enum_feature` can be used to build feature signatures;
-   `featureVec` for vectors, which are list of values with each value living in the domain of the corresponding feature.

`Xp.mli` contains the module type `InputProblem` encapsulating the parameters for an explanation problem:
-   `n` is the number of features;
-   `fs` is the list of all features;
-   `K` is a module encapsulating the type of the classifier's output---_for classifiers that return strings, the implementation `Utils.StringOT` will work;_
-   `t` is the type of classifiers;
-   `eval` is the evaluation function for classifiers;
-   `k` is the particular classifier to consider;
-   `v` is the particular instance to explain;
-   `S` is a implementation of sets over feature indexes---_the simplest is to instantiate this field using the `MakeFinSet` functor on a module containing the parameter `n`._
