open DT
open Features

type coq_class = string

type input_data = { n_features : int; features : featureList;
                    decision_tree : coq_class decisionTree;
                    instance : featureSpace }
