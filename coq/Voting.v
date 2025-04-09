
Require Import List Orders Arith Lia.
Require OrdersEx FMaps FMapFacts.
Import ListNotations.

(* Implementation of a voting function that computes the element with the
   most occurrences in a list.  A decidable order must be provided to
   select the minimum element if there are several candidates. *)

(* OrderedType restricted to Usual because count_occ needs the usual
   equality to be decidable *)
Module Type VotingSig (OT : UsualOrderedType).

    Module OTF : UsualOrderedTypeFull
        with Definition t := OT.t := OT_to_Full OT.
    Import OTF.

    Parameter vote : t -> list t -> t.

    Local Definition count_occ := count_occ eq_dec.

    Axiom vote_In : forall (x : t) (l : list t),
        In (vote x l) (x :: l).

    Axiom vote_count_le : forall (x : t) (l : list t) (y : t),
        count_occ (x :: l) y <= count_occ (x :: l) (vote x l).

    Axiom vote_count_max : forall (x : t) (l : list t) (y : t),
        count_occ (x :: l) y = count_occ (x :: l) (vote x l) ->
        le (vote x l) y.

End VotingSig.


Module Voting (OT : UsualOrderedType) : VotingSig OT.

    Module OTF : UsualOrderedTypeFull
        with Definition t := OT.t := OT_to_Full OT.
    Import OTF.

    (* The standard library uses another implementation of OrderedType
       for finite maps *)
    Module MOT_alt : OrderedType.MiniOrderedType
    with Definition t := OTF.t
    with Definition eq := OTF.eq
    with Definition lt := OTF.lt.
        Definition t := OTF.t.
        Definition eq := OTF.eq.
        Definition lt := OTF.lt.
        Definition eq_refl := @eq_refl t.
        Definition eq_sym := @eq_sym t.
        Definition eq_trans := @eq_trans t.
        Definition lt_trans : transitive t OTF.lt.
            unfold transitive. intros x y z.
            transitivity y; assumption.
        Defined.
        Definition lt_not_eq : forall x y, lt x y -> x <> y.
            intros x y H1 H2. subst x.
            apply irreflexivity with (x := y). assumption.
        Defined.
        Definition compare x y :=
            match CompSpec2Type (OTF.compare_spec x y) with
            | CompEqT _ _ Heq => OrderedType.EQ Heq
            | CompLtT _ _ Hlt => OrderedType.LT Hlt
            | CompGtT _ _ Hgt => OrderedType.GT Hgt
            end.
    End MOT_alt.

    Module OT_alt : OrderedType.OrderedType
        with Definition t := OTF.t
        with Definition eq := OTF.eq
        with Definition lt := OTF.lt :=
        OrderedType.MOT_to_OT MOT_alt.

    Module TMap : FMapInterface.S with Module E := OT_alt := FMapList.Make OT_alt.
    Module TMapFacts := FMapFacts.OrdProperties TMap.

    Local Definition count_occ := count_occ eq_dec.

    Import TMap TMapFacts TMapFacts.P TMapFacts.P.F.

    Local Definition map := TMap.t nat.
    Local Definition t := OTF.t.


    Lemma Add_spec_1 {A : Type} : forall k e (m m' : TMap.t A),
        Add k e m m' -> Equal m' (add k e m).
    Proof. unfold Equal; intros; rewrite <- H; reflexivity. Qed.

    Lemma Add_spec_2 {A : Type} : forall k e (m m' : TMap.t A),
        Equal m' (add k e m) -> Add k e m m'.
    Proof. unfold Add; intros; rewrite <- H; reflexivity. Qed.

    Lemma add_commutes {A : Type} : forall k k' e e' (m : TMap.t A),
        k <> k' ->
        Equal (add k e (add k' e' m)) (add k' e' (add k e m)).
    Proof.
        intros k k' e e' m H; unfold Equal; intros k'';
        destruct (eq_dec k k''); [| destruct (eq_dec k' k'')];
            [ rewrite add_eq_o, add_neq_o, add_eq_o
            | rewrite add_neq_o, 2add_eq_o
            | rewrite 4add_neq_o ];
        now try (intros abs; apply H; rewrite abs).
    Qed.

    Lemma Add_nempty {A : Type} : forall k e (m m' : TMap.t A),
        Add k e m m' -> ~ Empty m'.
    Proof.
        intros k e m m' H abs;
        eapply abs; rewrite Add_spec_1; [| apply H];
        apply add_1; reflexivity.
    Qed.


    Section CountOccurrences.

        (* We first build a map that pairs every element in the list [l] to 
           its number of occurrences in [l]. *)

        Fixpoint count_all_occ (l : list t) (acc : map) : map :=
            match l with
            | [] => acc
            | x :: t =>
                match find x acc with
                | Some n => count_all_occ t (add x (S n) acc)
                | None => count_all_occ t (add x 1 acc)
                end
            end.

        Program Instance count_all_occ_compat : Proper (Logic.eq ==> Equal ==> Equal) count_all_occ.
        Next Obligation.
            intros l l' Heql; subst l'.
            induction l as [| x t IH ]; intros m m' Heqm; simpl.
            -   assumption.
            -   rewrite <- Heqm.
                destruct (find x m);
                    apply IH; rewrite Heqm; reflexivity.
        Defined.


        Lemma count_all_occ_spec_1 : forall (acc : map),
            count_all_occ [] acc = acc.
        Proof. reflexivity. Qed.

        Lemma count_all_occ_spec_2 : forall (x : t) (t : list t) (n : nat) (acc : map),
            find x acc = Some n ->
            count_all_occ (x :: t) acc = count_all_occ t (add x (S n) acc).
        Proof. intros x t n acc H; simpl; rewrite H; reflexivity. Qed.

        Lemma count_all_occ_spec_3 : forall (x : t) (t : list t) (acc : map),
            find x acc = None ->
            count_all_occ (x :: t) acc = count_all_occ t (add x 1 acc).
        Proof. intros x t acc H; simpl; rewrite H; reflexivity. Qed.


        Lemma count_all_occ_app : forall (l1 l2 : list t) (acc : map),
            count_all_occ (l1 ++ l2) acc = count_all_occ l2 (count_all_occ l1 acc).
        Proof.
            intros l1 l2; induction l1 as [| x t IH ]; intros acc;
                try reflexivity;
            now simpl; destruct (find x acc); rewrite IH.
        Qed.


        Lemma count_all_occ_commute_first_two : forall (x y : t) (t : list t) (acc : map),
            Equal (count_all_occ (x :: y :: t) acc) (count_all_occ (y :: x :: t) acc).
        Proof.
            intros x y t acc; destruct (eq_dec x y) as [ Heq | Hneq ]; simpl.
            -   rewrite Heq; destruct (find y acc);
                now rewrite Heq, add_eq_o, Heq.
            -   destruct (find x acc) as [n1 |] eqn:H1;
                destruct (find y acc) as [n2 |] eqn:H2;
                now rewrite 2add_neq_o, H1, H2, add_commutes.
        Qed.

        Lemma count_all_occ_transpose : forall (x : t) (t : list t) (acc : map),
            Equal (count_all_occ (x :: t) acc) (count_all_occ [x] (count_all_occ t acc)).
        Proof.
            intros x t; induction t as [| y t' IH ]; intros acc;
                try reflexivity;
            now rewrite count_all_occ_commute_first_two;
            replace (y :: x :: t') with ([y] ++ (x :: t')); try reflexivity;
            rewrite count_all_occ_app, IH, <- count_all_occ_app with (l1 := [y]).
        Qed.

        Lemma count_all_occ_app_rev : forall (l1 l2 : list t) (acc : map),
            Equal (count_all_occ (l1 ++ l2) acc) (count_all_occ l1 (count_all_occ l2 acc)).
        Proof.
            intros l1; induction l1 as [| x t IH ]; intros l2 acc;
                try reflexivity.
            now replace ((x :: t) ++ l2) with (x :: (t ++ l2)); try reflexivity;
            rewrite count_all_occ_transpose, <- count_all_occ_app, <- app_assoc,
                IH, count_all_occ_app, <- count_all_occ_app.
        Qed.


        Lemma count_all_occ_find_cons_eq : forall (x : t) (t : list t) (n : nat) (acc : map),
            find x (count_all_occ t acc) = Some n ->
            find x (count_all_occ (x :: t) acc) = Some (S n).
        Proof.
            intros x t n acc H; rewrite count_all_occ_transpose; simpl;
            rewrite H; apply add_eq_o; reflexivity.
        Qed.

        Lemma count_all_occ_find_cons_neq : forall (x y : t) (t : list t) (acc : map),
            x <> y ->
            find x (count_all_occ (y :: t) acc) = find x (count_all_occ t acc).
        Proof.
            intros x y t acc H; rewrite count_all_occ_transpose; simpl;
            destruct (find y (count_all_occ t acc)); rewrite add_neq_o; auto.
        Qed.


        Lemma count_all_occ_find_1 : forall (l : list t) (x : t) (n : nat) (acc : map),
            find x acc = Some n ->
            find x (count_all_occ l acc) = Some (count_occ l x + n).
        Proof.
            intros l x n acc H; induction l as [| y t IH ];
                try assumption;
            unfold count_occ;
            destruct (eq_dec x y) as [ Heq | Hneq ].
            -   rewrite <- Heq, count_occ_cons_eq, Nat.add_succ_l; try reflexivity;
                apply count_all_occ_find_cons_eq, IH; assumption.
            -   rewrite count_occ_cons_neq, count_all_occ_find_cons_neq; try auto;
                apply IH.
        Qed.

        Lemma count_all_occ_find_2 : forall (l : list t) (x : t) (acc : map),
            ~ List.In x l ->
            find x (count_all_occ l acc) = find x acc.
        Proof.
            intros l x acc H; induction l as [| y t IH ];
                try reflexivity;
            rewrite not_in_cons in H; destruct H;
            rewrite count_all_occ_find_cons_neq; try auto;
            apply IH; assumption.
        Qed.

        Lemma count_all_occ_find_3 : forall (l : list t) (x : t) (acc : map),
            find x acc = None ->
            List.In x l ->
            find x (count_all_occ l acc) = Some (count_occ l x).
        Proof.
            intros l x acc H1 H2; induction l as [| y t IH ];
                try (now inversion H2).
            unfold count_occ;
            destruct (eq_dec y x) as [ Heqx | Hneqx ];
            destruct (in_dec eq_dec x t) as[ Hin | Hnin ].
            -   rewrite count_occ_cons_eq, Heqx; try auto;
                now apply count_all_occ_find_cons_eq, IH.
            -   rewrite count_occ_cons_eq, Heqx,
                    (proj1 (@count_occ_not_In Voting.t OTF.eq_dec t x) Hnin); (* ugh *)
                    try auto;
                simpl; rewrite H1, count_all_occ_find_2; try assumption;
                now apply add_eq_o.
            -   rewrite count_occ_cons_neq, count_all_occ_find_cons_neq;
                    try auto.
            -   inversion H2; contradiction.
        Qed.

        Lemma count_all_occ_find_4 : forall (l : list t) (x : t) (m n : nat) (acc : map),
            find x acc = Some m ->
            find x (count_all_occ l acc) = Some n ->
            n = count_occ l x + m.
        Proof.
            intros l x m n acc H1 H2;
            rewrite count_all_occ_find_1 with (n := m) in H2; try assumption;
            now inversion H2.
        Qed.

        Lemma count_all_occ_find_5 : forall (l : list t) (x : t) (n : nat) (acc : map),
            find x acc = None ->
            find x (count_all_occ l acc) = Some n ->
            List.In x l /\ n = count_occ l x.
        Proof.
            intros l x n acc H1 H2;
            destruct (in_dec eq_dec x l).
            -   rewrite count_all_occ_find_3 in H2; try assumption;
                now inversion H2.
            -   rewrite count_all_occ_find_2, H1 in H2; try assumption;
                now discriminate H2.
        Qed.

        Lemma count_all_occ_find_6 : forall (l : list t) (x : t) (acc : map),
            find x (count_all_occ l acc) = None ->
            find x acc = None /\ ~ List.In x l.
        Proof.
            intros l x acc H.
            destruct (in_dec eq_dec x l); destruct (find x acc) eqn:Hfind;
                try (now split).
            -   rewrite count_all_occ_find_1 with (n := n) in H;
                now inversion H.
            -   rewrite count_all_occ_find_3 in H; try assumption;
                now inversion H.
            -   rewrite count_all_occ_find_2, Hfind in H; try assumption;
                now inversion H.
        Qed.


        Lemma count_all_occ_In_1 : forall (l : list t) (acc : map) (x : t),
            In x acc -> In x (count_all_occ l acc).
        Proof.
            intros l acc x (n, H); eexists;
            apply find_2, count_all_occ_find_1, find_1, H.
        Qed.

        Lemma count_all_occ_In_2 : forall (l : list t) (acc : map) (x : t),
            List.In x l -> In x (count_all_occ l acc).
        Proof.
            intros l acc x H; destruct (find x acc) eqn:Hfind; eexists;
                [ apply find_2, count_all_occ_find_1, Hfind
                | apply find_2, count_all_occ_find_3; assumption ].
        Qed.

        Lemma count_all_occ_In_3 : forall (l : list t) (acc : map) (x : t),
            In x (count_all_occ l acc) -> In x acc \/ List.In x l.
        Proof.
            intros l acc x (n, H); destruct (find x acc) eqn:Hfind;
                try (left; eexists; apply find_2, Hfind);
            right; edestruct count_all_occ_find_5;
                [ apply Hfind
                | apply find_1, H
                | assumption ].
        Qed.

        Lemma count_all_occ_In_4 : forall (l : list t) (acc : map) (x : t),
            ~ List.In x l -> In x (count_all_occ l acc) -> In x acc.
        Proof. now intros l acc x H1 H2; edestruct count_all_occ_In_3; try (exact H2). Qed.

        Lemma count_all_occ_In_5 : forall (l : list t) (acc : map) (x : t),
            ~ In x acc -> In x (count_all_occ l acc) -> List.In x l.
        Proof. now intros l acc x H1 H2; edestruct count_all_occ_In_3; try (exact H2). Qed.

    End CountOccurrences.


    Section FindMaximum.

        (* Having built a map that contains the number of occurrences for
           every element of [l], we simply select the pair that corresponds
           to the maximum value.  Note that our maps are ordered by key, so
           if there are several candidates for the maximum, taking the first
           one ensures we are selecting the element that is minimal wrt. the
           order on [OTF]. *)

        Inductive findMaxSpec : map -> t -> t -> nat -> Prop :=
        | find_max_empty : forall m default,
            Empty m ->
            findMaxSpec m default default 0

        | find_max_next_le : forall m m' default k k' n n',
            Above k' m -> Add k' n' m m' ->
            n' <= n ->
            findMaxSpec m default k n -> findMaxSpec m' default k n

        | find_max_next_gt : forall m m' default k k' n n',
            Above k' m -> Add k' n' m m' ->
            n' > n ->
            findMaxSpec m default k n -> findMaxSpec m' default k' n'.

        Definition find_max_fold_f : t -> nat -> (t * nat) -> (t * nat) :=
            fun k' n' '(k, n) =>
                if n <? n' then
                    (k', n')
                else
                    (k, n).

        Definition find_max (m : map) (default : t) :=
            fold find_max_fold_f m (default, 0).

        Definition eqTNat : relation (t * nat) :=
            fun '(k, n) '(k', n') => OTF.eq k k' /\ n = n'.

        Program Instance eqTNatEquivalence : Equivalence eqTNat.
        Next Obligation.
            intros (k, n). unfold eqTNat.
            split; reflexivity.
        Defined.
        Next Obligation.
            intros (k, n) (k', n') (H1, H2). unfold eqTNat.
            split; symmetry; assumption.
        Defined.
        Next Obligation.
            intros (k, n) (k', n') (k'', n'') (H11, H12) (H21, H22). unfold eqTNat.
            split; [transitivity k' | transitivity n']; assumption.
        Defined.

        Program Instance eqTNatComp : Proper (OTF.eq ==> Logic.eq ==> eqTNat ==> eqTNat) find_max_fold_f.
        Next Obligation.
            intros k k' Heqk n n' Heqn (k'', n'') (k''', n''') (Heqk', Heqn').
            rewrite Heqk, Heqn, Heqk', Heqn'.
            reflexivity.
        Defined.


        Theorem find_max_correct : forall (m : map) (default k : t) (n : nat),
            findMaxSpec m default k n <-> eqTNat (find_max m default) (k, n).
        Proof.
            unfold find_max; split.
            -   intros H; induction H as [
                    m default HEmpty
                    | m m' default k k' n n' HNotIn HAdd HnLe Hfind IH
                    | m m' default k k' n n' HNotIn HAdd HnGt Hfind IH ];
                    try (destruct IH as (n'', IH));
                    try (
                        rewrite fold_Add_Above with (m1 := m) (x := k') (e := n'), IH;
                            try (exact eqTNatComp);
                            try (exact eqTNatEquivalence);
                            try assumption;
                        unfold find_max_fold_f;
                        destruct (Nat.ltb_spec n n');
                            try lia; reflexivity
                    );
                apply fold_Empty;
                    try (exact eqTNatEquivalence); (* why not automatic? *)
                assumption.
            -   generalize dependent n; generalize dependent k;
                apply map_induction_max with (m := m); clear m.
                +   intros m HEmpty k n H;
                    rewrite fold_Empty in H;
                        try (exact (flip_Equivalence eqTNatEquivalence));
                        try assumption;
                    destruct H as (H1, H2); rewrite H1, <- H2;
                    now constructor 1.
                +   intros m m' IH k' n' HAbove HAdd k n H;
                    rewrite fold_Add_Above with (m1 := m) (x := k') (e := n') in H;
                        try (exact (flip_Equivalence eqTNatEquivalence));
                        try solve_proper;
                        try assumption;
                    remember (fold find_max_fold_f m (default, 0)) as p;
                    destruct p as (k'', n'');
                    unfold find_max_fold_f in H; simpl in H;
                    destruct (Nat.ltb_spec n'' n') as [ Hlt | Hge ];
                    destruct H as (H1, H2); rewrite <- H1, <- H2 in *;
                        [ constructor 3 with (m := m) (k := k'') (n := n'')
                        | constructor 2 with (m := m) (k' := k') (n' := n') ];
                        try assumption;
                        try lia;
                    now apply IH.
        Qed.


        Lemma findMax_in_map : forall (m : map) (default k : t) (n : nat),
            findMaxSpec m default k n ->
            (k = default /\ n = 0) \/ MapsTo k n m.
        Proof.
            intros m default k n H; induction H as
                [ m default HEmpty
                | m m' default k k' n n' HAbove HAdd HnLe Hfind IH
                | m m' default k k' n n' HAbove HAdd HnGt Hfind IH ];
                try (now left).
            -   destruct IH as [ IH | IH ]; try (now left); right;
                rewrite Add_spec_1; try apply HAdd;
                rewrite add_neq_mapsto_iff; try assumption;
                cut (OT_alt.lt k k');
                    try (now intros Hlt; symmetry; apply OT_alt.lt_not_eq);
                apply HAbove; eexists; apply IH.
            -   right;
                rewrite Add_spec_1; try apply HAdd;
                rewrite add_mapsto_iff; now left.
        Qed.


        Lemma findMax_is_max : forall (m : map) (default k k' : t) (n n' : nat),
            findMaxSpec m default k n ->
            MapsTo k' n' m ->
            n >= n'.
        Proof.
            intros m default k k' n n' H1 H2; induction H1 as
                [ m default HEmpty
                | m m' default k k'' n n'' HAbove HAdd HnLe Hfind IH
                | m m' default k k'' n n'' HAbove HAdd HnGt Hfind IH ];
                try (now apply HEmpty in H2);
            rewrite Add_spec_1 in H2; try apply HAdd;
            destruct (eq_dec k' k'') as [ Heq | Hneq ];
                try (
                    rewrite Heq in *;
                    replace n' with n''; try lia;
                    apply find_1 in H2; rewrite add_eq_o in H2; try reflexivity;
                    now inversion H2
                );
            rewrite add_neq_mapsto_iff in H2;
                try (now intros abs; apply Hneq;  rewrite abs);
                [ apply IH, H2
                | cut (n >= n'); try lia; apply IH, H2 ].
        Qed.


        Definition map_positive (m : map) :=
            forall k n, MapsTo k n m -> n > 0.

        Lemma map_positive_Add_Above : forall (m m' : map) (k : t) (n : nat),
            Above k m ->
            Add k n m m' ->
            map_positive m' ->
            map_positive m.
        Proof.
            intros m m' k n HAbove HAdd Hpos k' n' HMapsTo;
            apply Hpos with (k := k');
            rewrite Add_spec_1; try apply HAdd;
            apply add_2; try assumption;
            cut (OT_alt.lt k' k);
                try (now intros Hlt; symmetry; apply OT_alt.lt_not_eq);
            apply HAbove; eexists; apply HMapsTo.
        Qed.


        Lemma findMax_positive : forall (m : map) (default k : t) (n : nat),
            ~ Empty m ->
            map_positive m ->
            findMaxSpec m default k n ->
            n > 0.
        Proof.
            intros m default k n Hnempty Hpos Hspec;
            induction Hspec as 
                [ m default HEmpty
                | m m' default k k'' n n'' HAbove HAdd HnLe Hfind IH
                | m m' default k k'' n n'' HAbove HAdd HnGt Hfind IH ];
                try contradiction;
            assert (n'' > 0);
                try (
                    apply Hpos with (k := k'');
                    rewrite Add_spec_1; try apply HAdd;
                    now apply add_1
                );
            apply map_positive_Add_Above with (m := m) (k := k'') (n := n'') in Hpos;
                try assumption;
                try (now apply add_1);
            cut (~ Empty m);
                try (
                    inversion Hfind; try lia;
                    eapply Add_nempty; eassumption
                ).
        Qed.

        Lemma findMax_in_map_ndefault : forall (m : map) (default k : t) (n : nat),
            ~ Empty m ->
            map_positive m ->
            findMaxSpec m default k n ->
            MapsTo k n m.
        Proof.
            intros m default k n Hnempty Hpos Hspec;
            edestruct findMax_in_map as [ (_, Hn0) |]; [apply Hspec | | assumption];
            apply findMax_positive in Hspec; try assumption; lia.
        Qed.

        Lemma findMax_max_min_key : forall (m : map) (default k k' : t) (n : nat),
            ~ Empty m ->
            map_positive m ->
            findMaxSpec m default k n ->
            MapsTo k' n m ->
            le k k'.
        Proof.
            intros m default k k' n Hnempty Hpos Hspec;
            generalize dependent k';
            assert (n > 0);
                try (eapply findMax_positive; [| | apply Hspec]; assumption);
            induction Hspec as
                [ m default HEmpty
                | m m' default k k'' n n'' HAbove HAdd HnLe Hfind IH
                | m m' default k k'' n n'' HAbove HAdd HnGt Hfind IH ];
                try contradiction;
            intros k' HMapsTo;
            rewrite Add_spec_1 in HMapsTo; try apply HAdd;
            apply map_positive_Add_Above with (m := m) (k := k'') (n := n'') in Hpos;
                try assumption;
                try (now apply add_1);
            destruct (eq_dec k' k'') as [ Heq | Hneq ];
                try (now rewrite Heq; apply le_lteq; right).
            -   rewrite Heq; apply le_lteq; left;
                apply HAbove; eexists;
                apply findMax_in_map in Hfind as [ Hl | Hr ]; try lia;
                apply Hr.
            -   apply add_3 in HMapsTo; try (now symmetry);
                apply IH; try assumption;
                intros abs; eapply abs, HMapsTo.
            -   apply add_3 in HMapsTo; try (now symmetry);
                cut (n >= n''); try lia;
                eapply findMax_is_max with (k' := k'); [apply Hfind | assumption].
        Qed.


        Lemma find_max_in_map : forall (m : map) (default k : t) (n : nat),
            find_max m default = (k, n) ->
            (k = default /\ n = 0) \/ MapsTo k n m.
        Proof.
            intros m default k n H;
            apply findMax_in_map, find_max_correct;
            now rewrite H.
        Qed.

        Lemma find_max_in_map_ndefault : forall (m : map) (default k : t) (n : nat),
            ~ Empty m ->
            map_positive m ->
            find_max m default = (k, n) ->
            MapsTo k n m.
        Proof.
            intros m default k n H1 H2 H3;
            eapply findMax_in_map_ndefault; try assumption; apply find_max_correct;
            now rewrite H3.
        Qed.

        Lemma find_max_is_max : forall (m : map) (default k k' : t) (n n' : nat),
            find_max m default = (k, n) ->
            MapsTo k' n' m ->
            n >= n'.
        Proof.
            intros m default k k' n n' H;
            eapply findMax_is_max, find_max_correct;
            now rewrite H.
        Qed.

        Lemma find_max_max_min_key : forall (m : map) (default k k' : t) (n : nat),
            ~ Empty m ->
            map_positive m ->
            find_max m default = (k, n) ->
            MapsTo k' n m ->
            le k k'.
        Proof.
            intros m default k k' H1 H2 H3 H4;
            eapply findMax_max_min_key; try assumption; apply find_max_correct;
            now rewrite H4.
        Qed.

    End FindMaximum.


    Definition vote (x : t) (l : list t) :=
        let '(x, _) :=
            find_max (count_all_occ (x :: l) (empty _)) x
        in x.


    Lemma count_all_occ_nempty (x : t) (l : list t) :
        ~ Empty (count_all_occ (x :: l) (empty _)).
    Proof.
        intros abs; eapply abs with (a := x);
        apply find_2, count_all_occ_find_3;
            try apply empty_o;
        now left.
    Qed.

    Lemma count_all_occ_MapsTo (x y : t) (l : list t) :
        List.In y (x :: l) ->
        MapsTo y (count_occ (x :: l) y) (count_all_occ (x :: l) (empty _)).
    Proof.
        intros; apply find_2, count_all_occ_find_3;
            try assumption;
        apply empty_o.
    Qed.

    Lemma count_all_occ_positive (x : t) (l : list t) :
        map_positive (count_all_occ (x :: l) (empty _)).
    Proof.
        intros k n HMapsTo; apply find_1 in HMapsTo;
        cut (List.In k (x :: l) /\ n = count_occ (x :: l) k);
            try (eapply count_all_occ_find_5; [apply empty_o | apply HMapsTo]);
        now intros (Hin, Heqn); rewrite Heqn; apply count_occ_In.
    Qed.


    Theorem vote_In : forall (x : t) (l : list t),
        List.In (vote x l) (x :: l).
    Proof.
        intros x l; unfold vote;
        remember (count_all_occ (x :: l) (empty nat)) as m;
        destruct (find_max m x) as (k, n) eqn:H;
        apply find_max_in_map in H as [|];
            try (now left);
        apply count_all_occ_In_5 with (acc := empty nat);
            try (now rewrite empty_in_iff);
        rewrite <- Heqm; eexists; eauto.
    Qed.


    Theorem vote_count_le : forall (x : t) (l : list t) (y : t),
        count_occ (x :: l) y <= count_occ (x :: l) (vote x l).
    Proof.
        intros x l y;
        pose proof (vote_In x l) as HvoteIn;
        unfold vote, count_occ in *;
        remember (count_all_occ (x :: l) (empty nat)) as m;
        destruct (find_max m x) as (k, n) eqn:H;
        destruct (in_dec eq_dec y (x :: l)) as [ Hin | Hnin ];
            try (
                rewrite count_occ_not_In in Hnin;
                rewrite Hnin; lia
            );
        apply find_max_is_max with (m := m) (k := k) (k' := y) (default := x);
            try (
                rewrite Heqm; apply find_2, count_all_occ_find_3;
                    try assumption;
                    try apply empty_o
            );
        replace (List.count_occ OTF.eq_dec (x :: l) k) with n;
            try assumption;
        apply find_max_in_map_ndefault in H;
            try (rewrite Heqm; apply count_all_occ_nempty);
            try (rewrite Heqm; apply count_all_occ_positive);
        edestruct count_all_occ_find_5;
            [ apply empty_o
            | rewrite <- Heqm; apply find_1, H
            | assumption ].
    Qed.


    Theorem vote_count_max : forall (x : t) (l : list t) (y : t),
        count_occ (x :: l) y = count_occ (x :: l) (vote x l) ->
        le (vote x l) y.
    Proof.
        intros x l y Hcount;
        assert (Hyin : List.In y (x :: l));
            try (
                cut (count_occ (x :: l) y > 0); [apply count_occ_In |];
                rewrite Hcount; apply count_occ_In, vote_In
            );
        apply count_all_occ_MapsTo in Hyin;
        unfold vote, count_occ in *;
        remember (count_all_occ (x :: l) (empty nat)) as m eqn:Heqm;
        destruct (find_max m x) as (k, n) eqn:H;
        apply find_max_max_min_key with (m := m) (default := x) (n := n);
            try (rewrite Heqm; apply count_all_occ_nempty);
            try (rewrite Heqm; apply count_all_occ_positive);
            try apply H;
        apply find_max_in_map_ndefault in H;
            try (rewrite Heqm; apply count_all_occ_nempty);
            try (rewrite Heqm; apply count_all_occ_positive);
        replace n with (List.count_occ OTF.eq_dec (x :: l) k);
            try (now rewrite <- Hcount);
        eapply MapsTo_fun; [| apply H]; rewrite Heqm;
        apply count_all_occ_MapsTo, count_all_occ_In_5 with (acc := empty _);
            try (now rewrite empty_in_iff);
        eexists; rewrite <- Heqm; apply H.
    Qed.

End Voting.