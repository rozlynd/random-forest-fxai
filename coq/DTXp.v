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

    Corollary boolConstraintEmptyUnsat :
        forall (c : boolConstraint) (x : bool),
            boolConstraintEmpty c = true -> ~ boolConstraintSat c x.
    Proof.
        intros c x H abs; now rewrite boolConstraintSatNotEmpty with (x := x) in H.
    Qed.

    Theorem boolConstraintWitnessSomeSat :
        forall (c : boolConstraint) (x : bool),
            boolConstraintWitness c = Some x -> boolConstraintSat c x.
    Proof. intros c x H; destruct c; destruct x; now inversion H. Qed.

    Corollary boolConstraintEmptyWitnessNone :
        forall (c : boolConstraint),
            boolConstraintEmpty c = true -> boolConstraintWitness c = None.
    Proof.
        intros c H; destruct (boolConstraintWitness c) as [x |] eqn:Hw; try reflexivity;
        exfalso; now apply boolConstraintEmptyUnsat with c x, boolConstraintWitnessSomeSat.
    Qed.

    Corollary boolConstraintWitnessSomeNonEmpty :
        forall (c : boolConstraint) (x : bool),
            boolConstraintWitness c = Some x -> boolConstraintEmpty c = false.
    Proof.
        intros c x H; now apply boolConstraintSatNotEmpty with (x := x), boolConstraintWitnessSomeSat.
    Qed.

    Theorem boolConstraintWitnessNoneEmpty :
        forall (c : boolConstraint),
            boolConstraintWitness c = None -> boolConstraintEmpty c = true.
    Proof. intros c H; destruct c; now inversion H. Qed.

    Corollary boolConstraintNonEmptyWitnessSome :
        forall (c : boolConstraint),
            boolConstraintEmpty c = false -> exists (x : bool), boolConstraintWitness c = Some x.
    Proof.
        intros c H; destruct (boolConstraintWitness) as [x |] eqn:Hw; try (now exists x);
        now rewrite boolConstraintWitnessNoneEmpty in H.
    Qed.

    Corollary boolConstraintNonEmptySat :
        forall (c : boolConstraint),
            boolConstraintEmpty c = false -> exists (x : bool), boolConstraintSat c x.
    Proof.
        intros c H; destruct boolConstraintNonEmptyWitnessSome with c as (x & H'); try assumption;
        exists x; now apply boolConstraintWitnessSomeSat.
    Qed.

    Theorem boolConstraintSatSplitLeft :
        forall (c : boolConstraint) (t : boolean_test) (x : bool),
            boolConstraintSat (boolConstraintLeftSplit t c) x <->
                boolConstraintSat c x /\ tests boolean_feature t x = true.
    Proof.
        intros c t x; split;
        [ intros H; destruct c; destruct t; destruct x; now inversion H
        | intros (H1 & H2); destruct c; destruct t; destruct x; now inversion H1 ].
    Qed.

    Corollary boolConstraintWitnessSplitLeft :
        forall (c : boolConstraint) (t : boolean_test) (x : bool),
            boolConstraintWitness (boolConstraintLeftSplit t c) = Some x ->
                tests boolean_feature t x = true.
    Proof.
        intros c t x H; now apply boolConstraintWitnessSomeSat, boolConstraintSatSplitLeft in H.
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

    Corollary boolConstraintWitnessSplitRight :
        forall (c : boolConstraint) (t : boolean_test) (x : bool),
            boolConstraintWitness (boolConstraintRightSplit t c) = Some x ->
                tests boolean_feature t x = false.
    Proof.
        intros c t x H; now apply boolConstraintWitnessSomeSat, boolConstraintSatSplitRight in H.
    Qed.

    Corollary boolConstraintSplitSat :
        forall (c : boolConstraint) (t : boolean_test) (x : bool),
            boolConstraintSat c x <->
                boolConstraintSat (boolConstraintLeftSplit t c) x \/
                boolConstraintSat (boolConstraintRightSplit t c) x.
    Proof.
        intros c t x; rewrite boolConstraintSatSplitLeft, boolConstraintSatSplitRight;
        split; intros H;
        [ now destruct (tests boolean_feature t x) eqn:Ht; [left | right]
        | now destruct H ].
    Qed.

    Corollary boolConstraintEmptySplit :
        forall (c : boolConstraint) (t : boolean_test),
            boolConstraintEmpty c =
                (boolConstraintEmpty (boolConstraintLeftSplit t c)
                && boolConstraintEmpty (boolConstraintRightSplit t c))%bool.
    Proof.
        intros c t;
        destruct (boolConstraintEmpty c) eqn:H;
        destruct (boolConstraintEmpty (boolConstraintLeftSplit t c)) eqn:Hl;
        destruct (boolConstraintEmpty (boolConstraintRightSplit t c)) eqn:Hr;
            try reflexivity; exfalso;
            try (
                apply boolConstraintNonEmptySat in Hr as (x & Hr);
                apply boolConstraintSatSplitRight in Hr as (Hr & _);
                apply boolConstraintSatNotEmpty in Hr; now rewrite Hr in H);
            try (
                apply boolConstraintNonEmptySat in Hl as (x & Hl);
                apply boolConstraintSatSplitLeft in Hl as (Hl & _);
                apply boolConstraintSatNotEmpty in Hl; now rewrite Hl in H);
        apply boolConstraintNonEmptySat in H as (x & H);
        destruct (tests boolean_feature t x) eqn:Ht;
        eapply boolConstraintEmptyUnsat; [apply Hl | idtac | apply Hr | idtac];
            try (now apply boolConstraintSatSplitLeft with (x := x));
            try (now apply boolConstraintSatSplitRight with (x := x)).
    Qed.

    Theorem boolConstraintInitFullNotEmpty :
        boolConstraintEmpty boolConstraintInitFull = false.
    Proof. reflexivity. Qed.

    Theorem boolConstraintWitnessSingleton :
        forall (x : bool),
            boolConstraintWitness (boolConstraintInitSingleton x) = Some x.
    Proof. intros x; destruct x; reflexivity. Qed.

    Corollary boolConstraintSatSingleton :
        forall (x : bool),
            boolConstraintSat (boolConstraintInitSingleton x) x.
    Proof. intros x; apply boolConstraintWitnessSomeSat, boolConstraintWitnessSingleton. Qed.

    Corollary boolConstraintInitSingletonNotEmpty :
        forall (x : bool),
            boolConstraintEmpty (boolConstraintInitSingleton x) = false.
    Proof. intros x; eapply boolConstraintSatNotEmpty, boolConstraintSatSingleton. Qed.

    Theorem boolConstraintSatSingletonUnique :
        forall (x y : bool),
            boolConstraintSat (boolConstraintInitSingleton x) y -> x = y.
    Proof. intros x y H; destruct x; destruct y; now inversion H. Qed.

    Corollary boolConstraintWitnessSingletonUnique :
        forall (x y : bool),
            boolConstraintWitness (boolConstraintInitSingleton x) = Some y -> x = y.
    Proof. intros x y H; now apply boolConstraintSatSingletonUnique, boolConstraintWitnessSomeSat. Qed.


    (* Definitions of witness, left/right split and init on the sum-type of constraints *)

    Variant fConstraint : forall (f : feature), getFeatureKind f -> Type :=
    | CBool : boolConstraint -> fConstraint boolean_feature isBooleanFeature
    | CFloat : floatConstraint -> fConstraint float_feature isContinuousFeature
    | CSEnum {s : StringSet.t} : senumConstraint s -> fConstraint (string_enum_feature s) (isStringEnumFeature s).

    Program Definition constraintEmpty {f : feature} (get : getFeatureKind f) : fConstraint f get -> bool :=
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

    Program Definition constraintSat {f : feature} (get : getFeatureKind f) : fConstraint f get -> dom f -> Prop :=
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

    Program Definition constraintWitness {f : feature} (get : getFeatureKind f) : fConstraint f get -> option (dom f) :=
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

    Program Definition constraintLeftSplit {f : feature} (get : getFeatureKind f) : testIndex f -> fConstraint f get -> fConstraint f get :=
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

    Program Definition constraintRightSplit {f : feature} (get : getFeatureKind f) : testIndex f -> fConstraint f get -> fConstraint f get :=
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

    Definition constraintInitFull {f : feature} (get : getFeatureKind f) : fConstraint f get :=
        match get with
        | isBooleanFeature => CBool boolConstraintInitFull
        | isContinuousFeature => CFloat floatConstraintInitFull
        | isStringEnumFeature s => CSEnum (senumConstraintInitFull s)
        end.

    Definition constraintInitSingleton {f : feature} (get : getFeatureKind f) : dom f -> fConstraint f get :=
        match get with
        | isBooleanFeature => fun x => CBool (boolConstraintInitSingleton x)
        | isContinuousFeature => fun x => CFloat (floatConstraintInitSingleton x)
        | isStringEnumFeature s => fun x => CSEnum (senumConstraintInitSingleton x)
        end.


    Section fConstraintFacts.

        Context {f : feature} (get : getFeatureKind f).

        Theorem constraintSatNotEmpty :
            forall (c : fConstraint f get) (x : dom f),
                constraintSat get c x -> constraintEmpty get c = false.
        Admitted.

        Corollary constraintEmptyUnsat :
            forall (c : fConstraint f get) (x : dom f),
                constraintEmpty get c = true -> ~ constraintSat get c x.
        Proof.
            intros c x H abs; now rewrite constraintSatNotEmpty with (x := x) in H.
        Qed.

        Theorem constraintWitnessSomeSat :
            forall (c : fConstraint f get) (x : dom f),
                constraintWitness get c = Some x -> constraintSat get c x.
        Admitted.

        Corollary constraintEmptyWitnessNone :
            forall (c : fConstraint f get),
                constraintEmpty get c = true -> constraintWitness get c = None.
        Proof.
            intros c H; destruct (constraintWitness get c) as [x |] eqn:Hw; try reflexivity;
            exfalso; now apply constraintEmptyUnsat with c x, constraintWitnessSomeSat.
        Qed.

        Corollary constraintWitnessSomeNonEmpty :
            forall (c : fConstraint f get) (x : dom f),
                constraintWitness get c = Some x -> constraintEmpty get c = false.
        Proof.
            intros c x H; now apply constraintSatNotEmpty with (x := x), constraintWitnessSomeSat.
        Qed.

        Theorem constraintWitnessNoneEmpty :
            forall (c : fConstraint f get),
                constraintWitness get c = None -> constraintEmpty get c = true.
        Admitted.

        Corollary constraintNonEmptyWitnessSome :
            forall (c : fConstraint f get),
                constraintEmpty get c = false -> exists (x : dom f), constraintWitness get c = Some x.
        Proof.
            intros c H; destruct (constraintWitness) as [x |] eqn:Hw; try (now exists x);
            now rewrite constraintWitnessNoneEmpty in H.
        Qed.

        Corollary constraintNonEmptySat :
            forall (c : fConstraint f get),
                constraintEmpty get c = false -> exists (x : dom f), constraintSat get c x.
        Proof.
            intros c H; destruct constraintNonEmptyWitnessSome with c as (x & H'); try assumption;
            exists x; now apply constraintWitnessSomeSat.
        Qed.

        Theorem constraintSatSplitLeft :
            forall (c : fConstraint f get) (t : testIndex f) (x : dom f),
                constraintSat get (constraintLeftSplit get t c) x <->
                    constraintSat get c x /\ tests f t x = true.
        Admitted.

        Corollary constraintWitnessSplitLeft :
            forall (c : fConstraint f get) (t : testIndex f) (x : dom f),
                constraintWitness get (constraintLeftSplit get t c) = Some x ->
                    tests f t x = true.
        Proof.
            intros c t x H; now apply constraintWitnessSomeSat, constraintSatSplitLeft in H.
        Qed.

        Theorem constraintSatSplitRight :
            forall (c : fConstraint f get) (t : testIndex f) (x : dom f),
                constraintSat get (constraintRightSplit get t c) x <->
                    constraintSat get c x /\ tests f t x = false.
        Admitted.

        Corollary constraintWitnessSplitRight :
            forall (c : fConstraint f get) (t : testIndex f) (x : dom f),
                constraintWitness get (constraintRightSplit get t c) = Some x ->
                    tests f t x = false.
        Proof.
            intros c t x H; now apply constraintWitnessSomeSat, constraintSatSplitRight in H.
        Qed.

        Corollary constraintSplitSat :
            forall (c : fConstraint f get) (t : testIndex f) (x : dom f),
                constraintSat get c x <->
                    constraintSat get (constraintLeftSplit get t c) x \/
                    constraintSat get (constraintRightSplit get t c) x.
        Proof.
            intros c t x; rewrite constraintSatSplitLeft, constraintSatSplitRight;
            split; intros H;
            [ now destruct (tests f t x) eqn:Ht; [left | right]
            | now destruct H ].
        Qed.

        Corollary constraintEmptySplit :
            forall (c : fConstraint f get) (t : testIndex f),
                constraintEmpty get c =
                    (constraintEmpty get (constraintLeftSplit get t c)
                    && constraintEmpty get (constraintRightSplit get t c))%bool.
        Proof.
            intros c t;
            destruct (constraintEmpty get c) eqn:H;
            destruct (constraintEmpty get (constraintLeftSplit get t c)) eqn:Hl;
            destruct (constraintEmpty get (constraintRightSplit get t c)) eqn:Hr;
                try reflexivity; exfalso;
                try (
                    apply constraintNonEmptySat in Hr as (x & Hr);
                    apply constraintSatSplitRight in Hr as (Hr & _);
                    apply constraintSatNotEmpty in Hr; now rewrite Hr in H);
                try (
                    apply constraintNonEmptySat in Hl as (x & Hl);
                    apply constraintSatSplitLeft in Hl as (Hl & _);
                    apply constraintSatNotEmpty in Hl; now rewrite Hl in H);
            apply constraintNonEmptySat in H as (x & H);
            destruct (tests f t x) eqn:Ht;
            eapply constraintEmptyUnsat; [apply Hl | idtac | apply Hr | idtac];
                try (now apply constraintSatSplitLeft with (x := x));
                try (now apply constraintSatSplitRight with (x := x)).
        Qed.

        Theorem constraintInitFullNotEmpty :
            constraintEmpty get (constraintInitFull get) = false.
        Admitted.

        Theorem constraintWitnessSingleton :
            forall (x : dom f),
                constraintWitness get (constraintInitSingleton get x) = Some x.
        Admitted.

        Corollary constraintSatSingleton :
            forall (x : dom f),
                constraintSat get (constraintInitSingleton get x) x.
        Proof. intros x; apply constraintWitnessSomeSat, constraintWitnessSingleton. Qed.

        Corollary constraintInitSingletonNotEmpty :
            forall (x : dom f),
                constraintEmpty get (constraintInitSingleton get x) = false.
        Proof. intros x; eapply constraintSatNotEmpty, constraintSatSingleton. Qed.

        Theorem constraintSatSingletonUnique :
            forall (x y : dom f),
                constraintSat get (constraintInitSingleton get x) y -> x = y.
        Admitted.

        Corollary constraintWitnessSingletonUnique :
            forall (x y : dom f),
                constraintWitness get (constraintInitSingleton get x) = Some y -> x = y.
        Proof. intros x y H; now apply constraintSatSingletonUnique, constraintWitnessSomeSat. Qed.

    End fConstraintFacts.


    (* Vectors of constraints *)

    Inductive featureSpaceConstraint : forall {n : nat}, featureSig n -> Type :=
    | featureSpaceConstraintNil : featureSpaceConstraint featureSigNil
    | featureSpaceConstraintCons
        (f : feature) (get : getFeatureKind f) (c : fConstraint f get)
        {n : nat} {fs : featureSig n} (cs : featureSpaceConstraint fs) :
            featureSpaceConstraint (featureSigCons f get fs).

    (* HERE BE DRAGONS *)
    Local Fixpoint update {n : nat} {fs : featureSig n}
                          (cs : featureSpaceConstraint fs) {struct cs} :
                            forall (i : fin n),
                                (forall (get : getFeatureKind (getFeature fs i)),
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
                | F1 => fun fs cs _ ap => featureSpaceConstraintCons f get (ap get c) cs
                | FS i => fun fs cs k ap => featureSpaceConstraintCons f get c (k i ap)
                end fs cs (update cs)
        end.

    Fixpoint empty {n : nat} {fs : featureSig n} (cs : featureSpaceConstraint fs) : bool :=
        match cs with
        | featureSpaceConstraintNil => true
        | featureSpaceConstraintCons f get c cs =>
            constraintEmpty get c && empty cs
        end.

    Fixpoint witness {n : nat} {fs : featureSig n} (cs : featureSpaceConstraint fs) : option (featureVec fs) :=
        match cs with
        | featureSpaceConstraintNil => Some (featureVecNil)
        | featureSpaceConstraintCons f get c cs =>
            match constraintWitness get c with
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
        fun cs => update cs i (fun get => constraintLeftSplit get t).

    Definition splitRight {n : nat} {fs : featureSig n} (i : fin n) (t : testIndex (getFeature fs i)) :
            featureSpaceConstraint fs -> featureSpaceConstraint fs :=
        fun cs => update cs i (fun get => constraintRightSplit get t).

    Fixpoint init {n : nat} (X : fin n -> bool) {fs : featureSig n} (vs : featureVec fs) : featureSpaceConstraint fs :=
        match vs in @featureVec n fs return (fin n -> bool) -> featureSpaceConstraint fs with
        | featureVecNil => fun _ => featureSpaceConstraintNil
        | @featureVecCons f get x _ fs vs => fun X =>
            let c :=
                if X F1 then constraintInitFull get
                else constraintInitSingleton get x
            in
            featureSpaceConstraintCons f get c (init (fun k => X (FS k)) vs)
        end X.


    Theorem constraintSpaceWitnessNotEmpty :
        forall {n : nat} (fs : featureSig n) (cs : featureSpaceConstraint fs),
            empty cs = false <->
                exists (v : featureVec fs), witness cs = Some v.
    Admitted.

    Corollary constraintSpaceWitnessEmpty :
        forall {n : nat} (fs : featureSig n) (cs : featureSpaceConstraint fs),
            empty cs = true <-> witness cs = None.
    Admitted.

    Theorem constraintSpaceEmptySplit :
        forall {n : nat} (fs : featureSig n) (i : fin n) (t : testIndex (getFeature fs i)) (cs : featureSpaceConstraint fs),
            empty cs = (empty (splitLeft i t cs) && empty (splitRight i t cs))%bool.
    Admitted.

    Theorem constraintSpaceWitnessLeftSplit :
        forall {n : nat} (fs : featureSig n) (i : fin n) (t : testIndex (getFeature fs i)) (cs : featureSpaceConstraint fs) (v : featureVec fs),
            witness (splitLeft i t cs) = Some v ->
                featureTest' v i t = true.
    Admitted.

    Theorem constraintSpaceWitnessRightSplit :
        forall {n : nat} (fs : featureSig n) (i : fin n) (t : testIndex (getFeature fs i)) (cs : featureSpaceConstraint fs) (v : featureVec fs),
            witness (splitRight i t cs) = Some v ->
                featureTest' v i t = false.
    Admitted.

    Theorem constraintSpaceInitNotEmpty :
        forall {n : nat} (fs : featureSig n) (X : fin n -> bool) (vs : featureVec fs),
            empty (init X vs) = false.
    Admitted.

    Theorem constraintSpaceInitWitness :
        forall {n : nat} (fs : featureSig n) (X : fin n -> bool) (vs vs' : featureVec fs) (i : fin n),
            witness (init X vs) = Some vs' -> X i = false -> getValue' vs' i = getValue' vs i.
    Admitted.


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

    Lemma init_constraintWitness :
        forall (X : S.t) (v v' : featureVec C.fs),
            witness (init X v) = Some v' -> FD.equiv (S.compl X) v v'.
    Proof.
        intros X v v' H i Hi; symmetry;
        eapply constraintSpaceInitWitness; [eassumption|];
        apply Bool.not_true_is_false; intros abs;
        apply S.In_compl in Hi; now apply Hi, S.mem_spec.
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
