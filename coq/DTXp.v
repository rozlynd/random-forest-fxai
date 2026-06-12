From RFXP Require Import Utils Features DT Xp Explainers.

Require Import Floats.


Module Type DTExplanationProblem <: ExplanationProblem :=
    FeatureSig <+ Output <+ DTOn <+ ClassifierInstance.

Module Type DTInputProblem <: InputProblem.
    Include DTExplanationProblem.
    Declare Module S : FinSet with Definition n := n.
End DTInputProblem.


Section FeatureSpaceConstraint.

    (* Representations for feature constraints *)

    Variant boolConstraint : Type :=
    | BEmpty
    | BTrue
    | BFalse
    | BAny.

    Variant floatConstraint : Type :=
    | FEmpty
    | FSingleton (a : float_std)
    | FRange (a b : float_std) (p : (proj1_sig a <? proj1_sig b)%float = true). (* [ a; b [ \ { -inf } *)

    Variant senumConstraint (s : StringSet.t) : Type :=
    | SEnum (p : StringSet.t) (q : StringSet.Subset p s).


    (* Check if a constraint is unsatisfiable *)

    Definition boolConstraintEmpty (c : boolConstraint) : bool :=
        match c with
        | BEmpty => true
        | _ => false
        end.

    Definition floatConstraintEmpty (c : floatConstraint) : bool :=
        match c with
        | FEmpty => true
        | _ => false
        end.

    Definition senumConstraintEmpty {s : StringSet.t} (c : senumConstraint s) : bool :=
        match c with
        | SEnum _ p _ => StringSet.is_empty p
        end.


    (* Constraint as predicate *)

    Definition boolConstraintSat (c : boolConstraint) (b : bool) : Prop :=
        match c with
        | BEmpty => False
        | BTrue => b = true
        | BFalse => b = false
        | BAny => True
        end.

    Definition floatConstraintSat (c : floatConstraint) (x : float_std) : Prop :=
        match c with
        | FEmpty => False
        | FSingleton a => (proj1_sig a =? proj1_sig x = true)%float
        | FRange a b _ => (proj1_sig a <=? proj1_sig x = true)%float /\ (proj1_sig x <? proj1_sig b = true)%float
        end.

    Definition senumConstraintSat {s : StringSet.t} (c : senumConstraint s) (x : string_enum s) : Prop :=
        match c with
        | SEnum _ p _ => StringSet.In (proj1_sig x) p
        end.


    (* Get a witness satisfying some constraint if one exists *)

    Definition boolConstraintWitness (c : boolConstraint) : option bool :=
        match c with
        | BEmpty => None
        | BTrue | BAny => Some true
        | BFalse => Some false
        end.

    Program Definition floatConstraintWitness (c : floatConstraint) : option float_std :=
        match c with
        | FEmpty => None
        | FSingleton a => Some a
        | FRange a b p =>
            (if is_infinity a then
                if is_infinity b then
                    Some (exist _ 0.0 _)
                else
                    Some (exist _ (next_down (proj1_sig b)) _)
            else
                Some a)%float
        end.
    Next Obligation. Admitted.

    Program Definition senumConstraintWitness {s : StringSet.t} (c : senumConstraint s) : option (string_enum s) :=
        match c with
        | SEnum _ p q =>
            match StringSet.choose p with
            | None => None
            | Some x => Some (exist _ x _)
            end
        end.
    Next Obligation. now apply q, choose_1. Qed.


    (* Split constraints on the left or right *)

    Definition boolConstraintLeftSplit (t : boolean_test) (c : boolConstraint) : boolConstraint :=
        match c with
        | BEmpty | BFalse => BEmpty
        | BTrue | BAny => BTrue
        end.

    Definition boolConstraintRightSplit (t : boolean_test) (c : boolConstraint) : boolConstraint :=
        match c with
        | BEmpty | BTrue => BEmpty
        | BFalse | BAny => BFalse
        end.

    Program Definition floatConstraintLeftSplit (t : float_test) (c : floatConstraint) : floatConstraint :=
        let '(float_lt x) := t in
        if is_infinity (proj1_sig x) then
            if get_sign (proj1_sig x) then
                c
            else
                FEmpty
        else
            match c with
            | FEmpty => FEmpty
            | FSingleton a =>
                if proj1_sig a <? proj1_sig x then
                    FSingleton a
                else
                    FEmpty
            | FRange a b p =>
                if proj1_sig a <? proj1_sig x then
                    if proj1_sig b <? proj1_sig x then
                        FRange a b p
                    else
                        FRange a x _
                else
                    FEmpty
            end%float.
    Next Obligation. Admitted.

    Program Definition floatConstraintRightSplit (t : float_test) (c : floatConstraint) : floatConstraint :=
        let '(float_lt x) := t in
        if is_infinity (proj1_sig x) then
            if get_sign (proj1_sig x) then
                FEmpty
            else
                c
        else
            match c with
            | FEmpty => FEmpty
            | FSingleton a =>
                if proj1_sig a <? proj1_sig x then
                    FEmpty
                else
                    FSingleton a
            | FRange a b p =>
                if proj1_sig b <? proj1_sig x then
                    FEmpty
                else
                    if proj1_sig a <? proj1_sig x then
                        FRange x b _
                    else
                        FRange a b p
            end%float.
    Next Obligation. Admitted.

    Program Definition senumConstraintLeftSplit {s : StringSet.t} (t : string_enum_test s) (c : senumConstraint s) : senumConstraint s :=
        let '(subset_mem _ filt) := t in
        match c with
        | SEnum _ p q => SEnum s (StringSet.filter filt p) _
        end.
    Next Obligation.
        intros x H; apply filter_1 in H; try auto.
        intros y z E; now rewrite E.
    Qed.

    Program Definition senumConstraintRightSplit {s : StringSet.t} (t : string_enum_test s) (c : senumConstraint s) : senumConstraint s :=
        let '(subset_mem _ filt) := t in
        match c with
        | SEnum _ p q => SEnum s (StringSet.filter (fun x => negb (filt x)) p) _
        end.
    Next Obligation.
        intros x H; apply filter_1 in H; try auto.
        intros y z E; now rewrite E.
    Qed.


    (* Initialize a constraint as either the full domain or a singleton value *)

    Definition boolConstraintInitFull := BAny.
    Program Definition floatConstraintInitFull := FRange (exist _ neg_infinity _) (exist _ infinity _) _.
    Definition senumConstraintInitFull (s : StringSet.t) := SEnum s s (@Subset_refl _).

    Definition boolConstraintInitSingleton (b : bool) :=
        if b then BTrue
        else BFalse.

    Definition floatConstraintInitSingleton (x : float_std) := FSingleton x.

    Program Definition senumConstraintInitSingleton {s : StringSet.t} (x : string_enum s) :=
        SEnum s (StringSet.singleton (proj1_sig x)) _.
    Next Obligation.
        intros y H; destruct x;
        apply singleton_1 in H; now rewrite <- H.
    Qed.


    (* Facts about individual constraints *)

    Theorem boolConstraintSatNotEmpty :
        forall (c : boolConstraint) (x : bool),
            boolConstraintSat c x -> boolConstraintEmpty c = false.
    Proof. intros c x H; destruct c; destruct x; now inversion H. Qed.

    Theorem boolConstraintWitnessSomeSat :
        forall (c : boolConstraint) (x : bool),
            boolConstraintWitness c = Some x -> boolConstraintSat c x.
    Proof. intros c x H; destruct c; destruct x; now inversion H. Qed.

    Theorem boolConstraintWitnessNoneEmpty :
        forall (c : boolConstraint),
            boolConstraintWitness c = None -> boolConstraintEmpty c = true.
    Proof. intros c H; destruct c; now inversion H. Qed.

    Theorem boolConstraintSatSplitLeft :
        forall (c : boolConstraint) (t : boolean_test) (x : bool),
            boolConstraintSat (boolConstraintLeftSplit t c) x <->
                boolConstraintSat c x /\ tests boolean_feature t x = true.
    Proof.
        intros c t x; split;
        [ intros H; destruct c; destruct t; destruct x; now inversion H
        | intros (H1 & H2); destruct c; destruct t; destruct x; now inversion H1 ].
    Qed.

    Theorem boolConstraintSatSplitRight :
        forall (c : boolConstraint) (t : boolean_test) (x : bool),
            boolConstraintSat (boolConstraintRightSplit t c) x <->
                boolConstraintSat c x /\ tests boolean_feature t x = false.
    Proof.
        intros c t x; split;
        [ intros H; destruct c; destruct t; destruct x; now inversion H
        | intros (H1 & H2); destruct c; destruct t; destruct x; now inversion H1 ].
    Qed.

    Theorem boolConstraintInitFullNotEmpty :
        boolConstraintEmpty boolConstraintInitFull = false.
    Proof. reflexivity. Qed.

    Theorem boolConstraintWitnessSingleton :
        forall (x : bool),
            boolConstraintWitness (boolConstraintInitSingleton x) = Some x.
    Proof. intros x; destruct x; reflexivity. Qed.

    Theorem boolConstraintSatSingletonUnique :
        forall (x y : bool),
            boolConstraintSat (boolConstraintInitSingleton x) y -> x = y.
    Proof. intros x y H; destruct x; destruct y; now inversion H. Qed.


    (* Definitions of witness, left/right split and init on the sum-type of constraints *)

    Variant fConstraint : forall (f : feature), getFeatureKind f -> Type :=
    | CBool : boolConstraint -> fConstraint boolean_feature isBooleanFeature
    | CFloat : floatConstraint -> fConstraint float_feature isContinuousFeature
    | CSEnum {s : StringSet.t} : senumConstraint s -> fConstraint (string_enum_feature s) (isStringEnumFeature s).

    Program Definition constraintEmpty {f : feature} {get : getFeatureKind f} : fConstraint f get -> bool :=
        match get in getFeatureKind f
                    return fConstraint f get -> bool
        with
        | isBooleanFeature => fun c =>
            match c with
            | CBool c => boolConstraintEmpty c
            | _ => False_rect _ _
            end
        | isContinuousFeature => fun c =>
            match c with
            | CFloat c => floatConstraintEmpty c
            | _ => False_rect _ _
            end
        | isStringEnumFeature s => fun c =>
            match c with
            | CSEnum c => fun s => @senumConstraintEmpty s c
            | _ => fun _ => False_rect _ _
            end s
        end.
    Admit Obligations.

    Program Definition constraintSat {f : feature} {get : getFeatureKind f} : fConstraint f get -> dom f -> Prop :=
        match get in getFeatureKind f
                    return fConstraint f get -> dom f -> Prop
        with
        | isBooleanFeature => fun c =>
            match c with
            | CBool c => fun x => boolConstraintSat c x
            | _ => fun _ => False_rect _ _
            end
        | isContinuousFeature => fun c =>
            match c with
            | CFloat c => fun x => floatConstraintSat c x
            | _ => fun _ => False_rect _ _
            end
        | isStringEnumFeature s => fun c =>
            match c with
            | CSEnum c => fun x => senumConstraintSat c x
            | _ => fun _ => False_rect _ _
            end
        end.
    Admit Obligations.

    Program Definition constraintWitness {f : feature} {get : getFeatureKind f} : fConstraint f get -> option (dom f) :=
        match get in getFeatureKind f 
                    return fConstraint f get -> option (dom f)
        with
        | isBooleanFeature => fun c =>
            match c with
            | CBool c => boolConstraintWitness c
            | _ => False_rect _ _
            end
        | isContinuousFeature => fun c =>
            match c with
            | CFloat c => floatConstraintWitness c
            | _ => False_rect _ _
            end
        | isStringEnumFeature s => fun c =>
            match c with
            | CSEnum c => fun s => @senumConstraintWitness s c
            | _ => fun _ => False_rect _ _
            end s
        end.
    Admit Obligations.

    Program Definition constraintLeftSplit {f : feature} {get : getFeatureKind f} : testIndex f -> fConstraint f get -> fConstraint f get :=
        match get with
        | isBooleanFeature => fun t c =>
            match c with
            | CBool c => CBool (boolConstraintLeftSplit t c)
            | _ => False_rect _ _
            end
        | isContinuousFeature => fun t c =>
            match c with
            | CFloat c => CFloat (floatConstraintLeftSplit t c)
            | _ => False_rect _ _
            end
        | isStringEnumFeature s => fun t c =>
            match c with
            | CSEnum c => CSEnum (senumConstraintLeftSplit t c)
            | _ => False_rect _ _
            end
        end.
    Admit Obligations.

    Program Definition constraintRightSplit {f : feature} {get : getFeatureKind f} : testIndex f -> fConstraint f get -> fConstraint f get :=
        match get with
        | isBooleanFeature => fun t c =>
            match c with
            | CBool c => CBool (boolConstraintRightSplit t c)
            | _ => False_rect _ _
            end
        | isContinuousFeature => fun t c =>
            match c with
            | CFloat c => CFloat (floatConstraintRightSplit t c)
            | _ => False_rect _ _
            end
        | isStringEnumFeature s => fun t c =>
            match c with
            | CSEnum c => CSEnum (senumConstraintRightSplit t c)
            | _ => False_rect _ _
            end
        end.
    Admit Obligations.

    Definition constraintInitFull {f : feature} {get : getFeatureKind f} : fConstraint f get :=
        match get with
        | isBooleanFeature => CBool boolConstraintInitFull
        | isContinuousFeature => CFloat floatConstraintInitFull
        | isStringEnumFeature s => CSEnum (senumConstraintInitFull s)
        end.

    Definition constraintInitSingleton {f : feature} {get : getFeatureKind f} : dom f -> fConstraint f get :=
        match get with
        | isBooleanFeature => fun x => CBool (boolConstraintInitSingleton x)
        | isContinuousFeature => fun x => CFloat (floatConstraintInitSingleton x)
        | isStringEnumFeature s => fun x => CSEnum (senumConstraintInitSingleton x)
        end.


    Section fConstraintFacts.

        Context {f : feature} {get : getFeatureKind f}.

        Theorem constraintSatNotEmpty :
            forall (c : fConstraint f get) (x : dom f),
                constraintSat c x -> constraintEmpty c = false.
        Admitted.

        Theorem constraintWitnessSomeSat :
            forall (c : fConstraint f get) (x : dom f),
                constraintWitness c = Some x -> constraintSat c x.
        Admitted.

        Theorem constraintWitnessNoneEmpty :
            forall (c : fConstraint f get),
                constraintWitness c = None -> constraintEmpty c = true.
        Admitted.

        Theorem constraintSatSplitLeft :
            forall (c : fConstraint f get) (t : testIndex f) (x : dom f),
                constraintSat (constraintLeftSplit t c) x <->
                    constraintSat c x /\ tests f t x = true.
        Admitted.

        Theorem constraintSatSplitRight :
            forall (c : fConstraint f get) (t : testIndex f) (x : dom f),
                constraintSat (constraintRightSplit t c) x <->
                    constraintSat c x /\ tests f t x = false.
        Admitted.

        Theorem constraintInitFullNotEmpty :
            constraintEmpty (@constraintInitFull f get) = false.
        Admitted.

        Theorem constraintWitnessSingleton :
            forall (x : dom f),
                constraintWitness (@constraintInitSingleton f get x) = Some x.
        Admitted.

        Theorem constraintSatSingletonUnique :
            forall (x y : dom f),
                constraintSat (@constraintInitSingleton f get x) y -> x = y.
        Admitted.

    End fConstraintFacts.


    (* Vectors of constraints *)

    Inductive featureSpaceConstraint : forall {n : nat}, featureSig n -> Type :=
    | featureSpaceConstraintNil : featureSpaceConstraint featureSigNil
    | featureSpaceConstraintCons
        {f : feature} {get : getFeatureKind f} (c : fConstraint f get)
        {n : nat} {fs : featureSig n} (cs : featureSpaceConstraint fs) :
            featureSpaceConstraint (featureSigCons f get fs).

    (* HERE BE DRAGONS *)
    Local Fixpoint update {n : nat} {fs : featureSig n}
                          (cs : featureSpaceConstraint fs) {struct cs} :
                            forall (i : fin n),
                                (forall {get : getFeatureKind (getFeature fs i)},
                                    fConstraint (getFeature fs i) get -> fConstraint (getFeature fs i) get) ->
                                featureSpaceConstraint fs :=
        match cs in @featureSpaceConstraint n fs
                 return forall {i : fin n},
                            (forall (get : getFeatureKind (getFeature fs i)),
                                fConstraint (getFeature fs i) get -> fConstraint (getFeature fs i) get) ->
                            featureSpaceConstraint fs with
        | featureSpaceConstraintNil =>
            fun _ _ => featureSpaceConstraintNil
        | @featureSpaceConstraintCons f get c _ fs cs =>
            fun i =>
                match i in fin (S p)
                      return forall (fs : featureSig p) (cs : featureSpaceConstraint fs),
                        (forall (j : fin p),
                            (forall (get : getFeatureKind (getFeature fs j)),
                                fConstraint (getFeature fs j) get -> fConstraint (getFeature fs j) get) ->
                            featureSpaceConstraint fs) ->
                        (forall (get' : getFeatureKind (getFeature (featureSigCons f get fs) i)),
                            fConstraint (getFeature (featureSigCons f get fs) i) get' ->
                            fConstraint (getFeature (featureSigCons f get fs) i) get') ->
                        featureSpaceConstraint (featureSigCons f get fs) with
                | F1 => fun fs cs _ ap => featureSpaceConstraintCons (ap get c) cs
                | FS i => fun fs cs k ap => featureSpaceConstraintCons c (k i ap)
                end fs cs (update cs)
        end.

    Inductive sat : forall {n : nat} {fs : featureSig n}, featureSpaceConstraint fs -> featureVec fs -> Prop :=
    | featureSpaceSatNil : sat featureSpaceConstraintNil featureVecNil
    | featureSpaceSatCons {f : feature} {get : getFeatureKind f} (c : fConstraint f get) (x : dom f)
                          {n : nat} {fs : featureSig n} (cs : featureSpaceConstraint fs) (vs : featureVec fs) :
        constraintSat c x -> sat cs vs -> sat (featureSpaceConstraintCons c cs) (featureVecCons get x vs).

    Fixpoint empty {n : nat} {fs : featureSig n} (cs : featureSpaceConstraint fs) : bool :=
        match cs with
        | featureSpaceConstraintNil => true
        | featureSpaceConstraintCons f get c cs =>
            constraintEmpty get c && empty cs
        end.

    Fixpoint witness {n : nat} {fs : featureSig n} (cs : featureSpaceConstraint fs) : option (featureVec fs) :=
        match cs with
        | featureSpaceConstraintNil => Some (featureVecNil)
        | @featureSpaceConstraintCons _ get c _ _ cs =>
            match constraintWitness c with
            | None => None
            | Some x =>
                match witness cs with
                | None => None
                | Some vs => Some (featureVecCons get x vs)
                end
            end
        end.

    Definition splitLeft {n : nat} {fs : featureSig n} (i : fin n) (t : testIndex (getFeature fs i)) :
            featureSpaceConstraint fs -> featureSpaceConstraint fs :=
        fun cs => update cs i (fun _ => constraintLeftSplit t).

    Definition splitRight {n : nat} {fs : featureSig n} (i : fin n) (t : testIndex (getFeature fs i)) :
            featureSpaceConstraint fs -> featureSpaceConstraint fs :=
        fun cs => update cs i (fun _ => constraintRightSplit t).

    Fixpoint init {n : nat} (X : fin n -> bool) {fs : featureSig n} (vs : featureVec fs) : featureSpaceConstraint fs :=
        match vs in @featureVec n fs return (fin n -> bool) -> featureSpaceConstraint fs with
        | featureVecNil => fun _ => featureSpaceConstraintNil
        | featureVecCons _ x vs => fun X =>
            let c :=
                if X F1 then constraintInitFull
                else constraintInitSingleton x
            in
            featureSpaceConstraintCons c (init (fun k => X (FS k)) vs)
        end X.


    Section fConstraintSpaceFacts.

        Context {n : nat} {fs : featureSig n}.

        Theorem constraintSpaceSatNotEmpty :
            forall (c : featureSpaceConstraint fs) (x : featureVec fs),
                sat c x -> empty c = false.
        Admitted.

        Corollary constraintSpaceEmptyUnsat :
            forall (c : featureSpaceConstraint fs) (x : featureVec fs),
                empty c = true -> ~ sat c x.
        Proof.
            intros c x H abs; now rewrite constraintSpaceSatNotEmpty with (x := x) in H.
        Qed.

        Theorem constraintSpaceWitnessSomeSat :
            forall (c : featureSpaceConstraint fs) (x : featureVec fs),
                witness c = Some x -> sat c x.
        Admitted.

        Corollary constraintSpaceEmptyWitnessNone :
            forall (c : featureSpaceConstraint fs),
                empty c = true -> witness c = None.
        Proof.
            intros c H; destruct (witness c) as [x |] eqn:Hw; try reflexivity;
            exfalso; now apply constraintSpaceEmptyUnsat with c x, constraintSpaceWitnessSomeSat.
        Qed.

        Corollary constraintSpaceWitnessSomeNonEmpty :
            forall (c : featureSpaceConstraint fs) (x : featureVec fs),
                witness c = Some x -> empty c = false.
        Proof.
            intros c x H; now apply constraintSpaceSatNotEmpty with (x := x), constraintSpaceWitnessSomeSat.
        Qed.

        Theorem constraintSpaceWitnessNoneEmpty :
            forall (c : featureSpaceConstraint fs),
                witness c = None -> empty c = true.
        Admitted.

        Corollary constraintSpaceNonEmptyWitnessSome :
            forall (c : featureSpaceConstraint fs),
                empty c = false -> exists (x : featureVec fs), witness c = Some x.
        Proof.
            intros c H; destruct (witness c) as [x |] eqn:Hw; try (now exists x);
            now rewrite constraintSpaceWitnessNoneEmpty in H.
        Qed.

        Corollary constraintSpaceNonEmptySat :
            forall (c : featureSpaceConstraint fs),
                empty c = false -> exists (x : featureVec fs), sat c x.
        Proof.
            intros c H; destruct constraintSpaceNonEmptyWitnessSome with c as (x & H'); try assumption;
            exists x; now apply constraintSpaceWitnessSomeSat.
        Qed.

        Theorem constraintSpaceSatSplitLeft :
            forall (c : featureSpaceConstraint fs) (i : fin n) (t : testIndex (getFeature fs i)) (x : featureVec fs),
                sat (splitLeft i t c) x <->
                    sat c x /\ tests (getFeature fs i) t (getValue' x i) = true.
        Admitted.

        Corollary constraintSpaceWitnessSplitLeft :
            forall (c : featureSpaceConstraint fs) (i : fin n) (t : testIndex (getFeature fs i)) (x : featureVec fs),
                witness (splitLeft i t c) = Some x ->
                    tests (getFeature fs i) t (getValue' x i) = true.
        Proof.
            intros c i t x H; now apply constraintSpaceWitnessSomeSat, constraintSpaceSatSplitLeft in H.
        Qed.

        Theorem constraintSpaceSatSplitRight :
            forall (c : featureSpaceConstraint fs) (i : fin n) (t : testIndex (getFeature fs i)) (x : featureVec fs),
                sat (splitRight i t c) x <->
                    sat c x /\ tests (getFeature fs i) t (getValue' x i) = false.
        Admitted.

        Corollary constraintSpaceWitnessSplitRight :
            forall (c : featureSpaceConstraint fs) (i : fin n) (t : testIndex (getFeature fs i)) (x : featureVec fs),
                witness (splitRight i t c) = Some x ->
                    tests (getFeature fs i) t (getValue' x i) = false.
        Proof.
            intros c i t x H; now apply constraintSpaceWitnessSomeSat, constraintSpaceSatSplitRight in H.
        Qed.

        Corollary constraintSpaceSplitSat :
            forall (c : featureSpaceConstraint fs) (i : fin n) (t : testIndex (getFeature fs i)) (x : featureVec fs),
                sat c x <->
                    sat (splitLeft i t c) x \/
                    sat (splitRight i t c) x.
        Proof.
            intros c i t x; rewrite constraintSpaceSatSplitLeft, constraintSpaceSatSplitRight;
            split; intros H;
            [ now destruct (tests (getFeature fs i) t (getValue' x i)) eqn:Ht; [left | right]
            | now destruct H ].
        Qed.

        Corollary constraintSpaceEmptySplit :
            forall (c : featureSpaceConstraint fs) (i : fin n) (t : testIndex (getFeature fs i)),
                empty c =
                    (empty (splitLeft i t c)
                    && empty (splitRight i t c))%bool.
        Proof.
            intros c i t;
            destruct (empty c) eqn:H;
            destruct (empty (splitLeft i t c)) eqn:Hl;
            destruct (empty (splitRight i t c)) eqn:Hr;
                try reflexivity; exfalso;
                try (
                    apply constraintSpaceNonEmptySat in Hr as (x & Hr);
                    apply constraintSpaceSatSplitRight in Hr as (Hr & _);
                    apply constraintSpaceSatNotEmpty in Hr; now rewrite Hr in H);
                try (
                    apply constraintSpaceNonEmptySat in Hl as (x & Hl);
                    apply constraintSpaceSatSplitLeft in Hl as (Hl & _);
                    apply constraintSpaceSatNotEmpty in Hl; now rewrite Hl in H);
            apply constraintSpaceNonEmptySat in H as (x & H);
            destruct (tests (getFeature fs i) t (getValue' x i)) eqn:Ht;
            eapply constraintSpaceEmptyUnsat; [apply Hl | idtac | apply Hr | idtac];
                try (now apply constraintSpaceSatSplitLeft with (x := x));
                try (now apply constraintSpaceSatSplitRight with (x := x)).
        Qed.

        Theorem constraintSpaceInitNotEmpty :
            forall (X : fin n -> bool) (vs : featureVec fs),
                empty (init X vs) = false.
        Admitted.

        Theorem constraintSpaceInitSatValuesUnique :
            forall (X : fin n -> bool) (vs vs' : featureVec fs) (i : fin n),
                sat (init X vs) vs' -> X i = false -> getValue' vs' i = getValue' vs i.
        Admitted.

    End fConstraintSpaceFacts.

End FeatureSpaceConstraint.


Module DtWCXpCheckerImpl (C : DT) (S : FinSet with Definition n := C.n).
    Module Import FD := FeatureSigDefs C S.

    Fixpoint refute_aux
            (c0 : C.K.t)
            (C : featureSpaceConstraint C.fs)
            (dt : C.t)
            : option (featureVec C.fs) :=
        match dt with
        | Leaf c =>
            if C.K.eq_dec c c0 then
                None
            else
                witness C
        | Node i test dt1 dt2 =>
            let Cleft := splitLeft i test C in
            let CRight := splitRight i test C in
            if empty Cleft then
                if empty CRight then
                    None
                else
                    refute_aux c0 CRight dt2
            else
                match refute_aux c0 Cleft dt1 with
                | Some r => Some r
                | None =>
                    if empty CRight then
                        None
                    else
                        refute_aux c0 CRight dt2
                end
        end.

    Lemma refute_aux_preserves_agrees :
        forall (v : featureVec C.fs) (c0 : C.K.t) (C : featureSpaceConstraint C.fs) (dt : C.t),
            True.
    Admitted.


    Definition init : S.t -> featureVec C.fs -> featureSpaceConstraint C.fs :=
        fun X => init (fun i => S.mem i X).

    Lemma init_constraintNotEmpty :
        forall (X : S.t) (v : featureVec C.fs),
            empty (init X v) = false.
    Proof. intros; apply constraintSpaceInitNotEmpty. Qed.

    Lemma init_constraintSatAgrees :
        forall (X : S.t) (v v' : featureVec C.fs),
            sat (init X v) v' -> FD.equiv (S.compl X) v v'.
    Proof.
        intros X v v' H i Hi; symmetry;
        eapply constraintSpaceInitSatValuesUnique;
        [ eassumption
        | apply Bool.not_true_is_false; intros abs;
          apply S.In_compl in Hi; now apply Hi, S.mem_spec ].
    Qed.


    Definition refute (dt : C.t) (v : featureVec C.fs) (X : S.t) : option (featureVec C.fs) :=
        refute_aux (C.eval dt v) (init X v) dt.

    Theorem refute_success_agrees :
        forall (dt : C.t) (v v' : featureVec C.fs) (X : S.t),
            refute dt v X = Some v' -> FD.equiv (S.compl X) v v'.
    Admitted.

    Theorem refute_success_contradicts :
        forall (dt : C.t) (v v' : featureVec C.fs) (X : S.t),
            refute dt v X = Some v' -> ~ C.K.eq (C.eval dt v) (C.eval dt v').
    Admitted.

    Theorem refute_fail :
        forall (dt : C.t) (v v' : featureVec C.fs) (X : S.t),
            refute dt v X = None -> FD.equiv (S.compl X) v v' -> C.K.eq (C.eval dt v) (C.eval dt v').
    Admitted.

End DtWCXpCheckerImpl.


Module DtWCXpChecker (Import E_ : DTInputProblem) : WCXpChecker with Module E := E_.
    Module E := E_.
    Module Import Xp := ExplainersDefs E.
    Module Impl := DtWCXpCheckerImpl E E.S.

    Definition checkWCXp (X : S.t) :=
        match Impl.refute E.k E.v X with
        | None => false
        | Some _ => true
        end.

    Theorem checkWCXpSound :
        forall X, Bool.reflect (Xp.WCXp X) (checkWCXp X).
    Proof.
        intros X; unfold checkWCXp;
        destruct (Impl.refute E.k E.v X) as [v |] eqn:Heq;
        constructor.
        -   exists v; split.
            +   eapply Impl.refute_success_agrees; eassumption.
            +   eapply Impl.refute_success_contradicts; eassumption.
        -   intros (v & Heqv & Hcont);
            eapply Hcont, Impl.refute_fail; eassumption.
    Defined.

End DtWCXpChecker.


Module DtAXpFinder (E_ : DTInputProblem) : AXpFinder with Module E := E_.
    Module Chk := DtWCXpChecker E_.
    Module Impl := AXpIterativeFinder E_ Chk.
    Include Impl.
End DtAXpFinder.

Module DtCXpFinder (E_ : DTInputProblem) : CXpFinder with Module E := E_.
    Module Chk := DtWCXpChecker E_.
    Module Impl := CXpIterativeFinder E_ Chk.
    Include Impl.
End DtCXpFinder.
