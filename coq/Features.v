Require Import List ZArith PrimFloat.

From RFXP Require Import Utils Enum.

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
    Variant boolean_test := bool_check.

    Definition boolean_feature : feature := {|
        dom := bool ;
        testIndex := boolean_test ;
        tests := fun 'bool_check b => b
    |}.

End BooleanFeature.


Section IntFeature.

    (* Fot ints, we allow testing equality and inequality *)
    Variant int_test := int_eq (a : Z.t) | int_le (a : Z.t).

    Definition int_feature : feature := {|
        dom := Z.t ;
        testIndex := int_test ;
        tests := fun t a =>
            match t with
            | int_eq b => (a =? b)%Z
            | int_le b => (a <=? b)%Z
            end
    |}.

End IntFeature.


Section FloatFeature.

    (* Every test for a float is a strict comparison to some threshold value *)
    Variant float_test := float_lt (y : float).

    Definition float_feature : feature := {|
        dom := float ;
        testIndex := float_test ;
        tests := fun t x =>
            match t with
            | float_lt y => (x <? y)%float
            end
    |}.

End FloatFeature.


Section EnumFeature.

    Import StringSet.

    (* Given a feature based on some enumeration of strings { s1, .., sn },
       there is a test for every subset of the enumeration: whether the
       feature value is a member of that subset *)
    Variant enum_test (s : StringSet.t) := subset_mem (p : enum s -> bool).

    Definition enum_feature (s : StringSet.t) : feature := {|
        dom := enum s ;
        testIndex := enum_test s ;
        tests := fun t x =>
            match t with
            | subset_mem _ p => p x
            end
    |}.

End EnumFeature.


(* We are only interested in two kinds of features: continuous and categorical.
   The only continuous feature we consider is float.  The only categorical
   features we consider are enumerations of strings. *)

Section FeaturesSpecial.

    Inductive allFeatures {n : nat} (P : feature -> Prop) : featureList n -> Prop :=
    | all_features (fs : featureList n) :
        (forall i, P (fs i)) -> allFeatures P fs.

    (* The sets that characterize our categorical features *)
    Context (ss : list StringSet.t).

    Inductive isEnum : feature -> Prop :=
    | is_enum' (s : StringSet.t) : In s ss -> isEnum (enum_feature s).

    Inductive isEnumOrFloat : feature -> Prop :=
    | is_enum (f : feature) : isEnum f -> isEnumOrFloat f
    | is_float : isEnumOrFloat float_feature.

    Context {n : nat} (fs : featureList n).

    Definition enum_list := allFeatures isEnum fs.
    Definition enum_float_list := allFeatures isEnumOrFloat fs.

End FeaturesSpecial.