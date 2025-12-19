open Features
open Utils

type 'class0 decisionTree =
| Leaf of 'class0
| Node of fin * testIndex * 'class0 decisionTree * 'class0 decisionTree

val evalDT : int -> featureSig -> 'a1 decisionTree -> featureVec -> 'a1
