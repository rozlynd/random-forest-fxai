open Features

type 'class0 decisionTree =
| Leaf of 'class0
| Node of featureIndex * testIndex * 'class0 decisionTree
   * 'class0 decisionTree

val evalDT : int -> featureList -> 'a1 decisionTree -> featureSpace -> 'a1
