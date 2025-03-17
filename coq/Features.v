Require Import List ZArith PrimFloat.

From RFXP Require Import Enum.

Section FeaturesGeneral.

    Definition indexed {X : Type} (A : X -> Type) := forall x : X, A x.
    Definition predicate (A : Type) := A -> bool.

    Record feature : Type := mk_feature {
        dom : Type ;
        testIndex : Type ;
        tests : indexed (fun _:testIndex => predicate dom)
    }.

    Definition featureIndex (n : nat) := { i : nat | i < n }.
    Definition featureList (n : nat) := indexed (fun _:featureIndex n => feature).

    Definition featureSpace {n : nat} (fs : featureList n) : Type :=
        indexed (fun fi:featureIndex n => dom (fs fi)).

    Definition getFeatureValue {n : nat}
                               {fs : featureList n}
                               (x : featureSpace fs)
                               (i : featureIndex n)
                               : dom (fs i) :=
        x i.

    Definition testFeature {n : nat}
                           {fs : featureList n}
                           (x : featureSpace fs)
                           (i : featureIndex n)
                           (t : testIndex (fs i))
                           : bool :=
        tests (fs i) t (x i).

End FeaturesGeneral.


Section BooleanFeature.

    (* The only test for a Boolean feature is to check the Boolean value *)
    Definition boolean_feature : feature := {|
        dom := bool ;
        testIndex := unit ;
        tests := fun _ b => b 
    |}.

End BooleanFeature.


Section IntFeature.

    Variant int_test := int_eq | int_le.

    (* Fot ints, we allow testing equality and inequality *)
    Definition int_feature : feature := {|
        dom := Z.t ;
        testIndex := int_test * Z.t ;
        tests := fun '(t, b) a =>
            match t with
            | int_eq => (a =? b)%Z
            | int_le => (a <=? b)%Z
            end
    |}.

End IntFeature.


Section FloatFeature.

    (* Every test for a float is a strict comparison to some threshold value *)
    Definition float_feature : feature := {|
        dom := float ;
        testIndex := float ;
        tests := fun y x => (x <? y)%float
    |}.

End FloatFeature.


Section EnumFeature.

    Import StringSet.

    (* Given a feature based on some enumeration of strings { s1, .., sn },
       there is a test for every subset of the enumeration: whether the
       feature value is a member of that subset *)
    Definition enum_feature (s : StringSet.t) : feature := {|
        dom := enum s ;
        testIndex := enum s -> bool ;
        tests := fun p x => p x
    |}.

End EnumFeature.