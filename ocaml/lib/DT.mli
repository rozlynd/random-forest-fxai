open Features

type 'class0 decisionTree =
| Leaf of 'class0
| Node of int * testIndex * 'class0 decisionTree * 'class0 decisionTree

val evalDT : int -> featureSig -> 'a1 decisionTree -> featureVec -> 'a1
