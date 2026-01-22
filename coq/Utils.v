Require Import List String Orders MSets Floats PrimFloat ZArith Arith.
Require Import Coq.Program.Equality.
Import ListNotations Lia.

(* String utils *)

Module StringOT : UsualOrderedType
    with Definition t := string :=
    String_as_OT.

Module StringOTF : UsualOrderedTypeFull
    with Definition t := string :=
    OT_to_Full StringOT.

Module StringSet : Sets
    with Module E := StringOT :=
    MSetList.Make StringOT.

Module StringSetProperties := OrdProperties StringSet.
Module StringSetMoreProperties := MSets.MSetFacts.WFactsOn StringOT StringSet.


Section StringEnumerations.

    Import StringSet.

    Definition string_enum (s : StringSet.t) : Type := { x : string | In x s }.

End StringEnumerations.


(* Float utils *)

Definition float_std := { x : float | is_nan x = false }.

Module FloatTTLB : TotalTransitiveLeBool
    with Definition t := float_std.

    Import Floats.FloatOps.

    Definition t := float_std.
    Definition leb (x y : float_std) :=
        PrimFloat.leb (proj1_sig x) (proj1_sig y).

    Definition compare_wd (x y : float_std) :
        { SFcompare (Prim2SF (proj1_sig x)) (Prim2SF (proj1_sig y)) = Some Eq } +
        { SFcompare (Prim2SF (proj1_sig x)) (Prim2SF (proj1_sig y)) = Some Lt } +
        { SFcompare (Prim2SF (proj1_sig x)) (Prim2SF (proj1_sig y)) = Some Gt }.
    Proof.
        destruct x as (x, Hx_wd); destruct y as (y, Hy_wd); simpl;
        destruct (Prim2SF x) as [ sx | sx | | sx mx ex ] eqn:Heqx;
        destruct (Prim2SF y) as [ sy | sy | | sy my ey ] eqn:Heqy;
        try (destruct sx);
        try (destruct sy);
        simpl;
            try (now constructor 1; constructor 1);
            try (now constructor 1; constructor 2);
            try (now constructor 2);
            try (
                unfold Prim2SF in Heqy;
                rewrite Hy_wd in Heqy;
                destruct (is_zero y); destruct (is_infinity y);
                destruct (Z.frexp y) as (r, exp);
                destruct (shr_fexp prec emax (Uint63.to_Z (normfr_mantissa r)) (BinInt.Z.sub exp prec) loc_Exact) as (shr, e');
                destruct (shr_m);
                    discriminate Heqy);
            try (
                unfold Prim2SF in Heqx;
                rewrite Hx_wd in Heqx;
                destruct (is_zero x); destruct (is_infinity x);
                destruct (Z.frexp x) as (r, exp);
                destruct (shr_fexp prec emax (Uint63.to_Z (normfr_mantissa r)) (BinInt.Z.sub exp prec) loc_Exact) as (shr, e');
                destruct (shr_m);
                    discriminate Heqx);
        destruct (BinInt.Z.compare ex ey);
        destruct (BinPos.Pos.compare_cont Eq mx my);
            try (now constructor 1; constructor 1);
            try (now constructor 1; constructor 2);
            try (now constructor 2).
    Defined.

    Definition nleb_gt (x y : float) :
        SFcompare (Prim2SF x) (Prim2SF y) = Some Gt ->
        SFcompare (Prim2SF y) (Prim2SF x) = Some Lt.
    Proof.
        destruct (Prim2SF x) as [ sx | sx | | sx mx ex ] eqn:Heqx;
        destruct (Prim2SF y) as [ sy | sy | | sy my ey ] eqn:Heqy;
        try (destruct sx);
        try (destruct sy);
        simpl;
            try (intros H; discriminate H);
            try reflexivity;
        replace (BinPos.Pos.compare_cont Eq) with (BinPos.Pos.compare);
            try reflexivity;
        destruct (BinInt.Z.compare_spec ex ey) as [ Heq | Hlt | Hgt ];
        destruct (BinInt.Z.compare_spec ey ex) as [ Heq' | Hlt' | Hgt' ];
        destruct (BinPos.Pos.compare_spec mx my) as [ Heq'' | Hlt'' | Hgt'' ];
        destruct (BinPos.Pos.compare_spec my mx) as [ Heq''' | Hlt''' | Hgt''' ];
        intros H;
            try reflexivity;
            try discriminate H;
            try (
                now subst;
                    try (now apply irreflexivity in Hlt);
                    try (now apply irreflexivity in Hlt');
                    try (now apply irreflexivity in Hlt'');
                    try (now apply irreflexivity in Hlt''');
                    try (now apply irreflexivity in Hgt);
                    try (now apply irreflexivity in Hgt');
                    try (now apply irreflexivity in Hgt'');
                    try (now apply irreflexivity in Hgt''');
                    try (now apply asymmetry in Hlt);
                    try (now apply asymmetry in Hlt');
                    try (now apply asymmetry in Hlt'');
                    try (now apply asymmetry in Hlt''');
                    try (now apply asymmetry in Hgt);
                    try (now apply asymmetry in Hgt');
                    try (now apply asymmetry in Hgt'');
                    try (now apply asymmetry in Hgt''')
            ).
    Defined.

    Definition leb_total (x y : float_std) :
        leb x y = true \/ leb y x = true.
    Proof.
        unfold leb; rewrite 2 leb_spec;
        unfold SFleb;
        destruct (compare_wd x y) as [[ H | H ] | H ];
        rewrite H;
            try (now left);
        now right; apply nleb_gt in H; rewrite H.
    Defined.

    Definition compare_eq_1 (x y z : float) :
        SFcompare (Prim2SF x) (Prim2SF y) = Some Eq ->
        SFcompare (Prim2SF y) (Prim2SF z) = SFcompare (Prim2SF x) (Prim2SF z).
    Proof.
        destruct (Prim2SF x) as [ sx | sx | | sx mx ex ] eqn:Heqx;
        destruct (Prim2SF y) as [ sy | sy | | sy my ey ] eqn:Heqy;
        try (destruct sx);
        try (destruct sy);
        simpl;
            try (intros H; discriminate H);
            try reflexivity;
        replace (BinPos.Pos.compare_cont Eq) with (BinPos.Pos.compare);
            try reflexivity;
        destruct (BinInt.Z.compare_spec ex ey) as [ Heq | Hlt | Hgt ];
        destruct (BinInt.Z.compare_spec ey ex) as [ Heq' | Hlt' | Hgt' ];
        destruct (BinPos.Pos.compare_spec mx my) as [ Heq'' | Hlt'' | Hgt'' ];
        destruct (BinPos.Pos.compare_spec my mx) as [ Heq''' | Hlt''' | Hgt''' ];
        intros H;
            try reflexivity;
            try discriminate H;
            try (
                now subst;
                    try (now apply irreflexivity in Hlt);
                    try (now apply irreflexivity in Hlt');
                    try (now apply irreflexivity in Hlt'');
                    try (now apply irreflexivity in Hlt''');
                    try (now apply irreflexivity in Hgt);
                    try (now apply irreflexivity in Hgt');
                    try (now apply irreflexivity in Hgt'');
                    try (now apply irreflexivity in Hgt''');
                    try (now apply asymmetry in Hlt);
                    try (now apply asymmetry in Hlt');
                    try (now apply asymmetry in Hlt'');
                    try (now apply asymmetry in Hlt''');
                    try (now apply asymmetry in Hgt);
                    try (now apply asymmetry in Hgt');
                    try (now apply asymmetry in Hgt'');
                    try (now apply asymmetry in Hgt''')
            ).
    Defined.

    Definition compare_eq_2 (x y z : float) :
        SFcompare (Prim2SF x) (Prim2SF y) = Some Eq ->
        SFcompare (Prim2SF z) (Prim2SF y) = SFcompare (Prim2SF z) (Prim2SF x).
    Proof.
        destruct (Prim2SF x) as [ sx | sx | | sx mx ex ] eqn:Heqx;
        destruct (Prim2SF y) as [ sy | sy | | sy my ey ] eqn:Heqy;
        try (destruct sx);
        try (destruct sy);
        simpl;
            try (intros H; discriminate H);
            try reflexivity;
        replace (BinPos.Pos.compare_cont Eq) with (BinPos.Pos.compare);
            try reflexivity;
        destruct (BinInt.Z.compare_spec ex ey) as [ Heq | Hlt | Hgt ];
        destruct (BinInt.Z.compare_spec ey ex) as [ Heq' | Hlt' | Hgt' ];
        destruct (BinPos.Pos.compare_spec mx my) as [ Heq'' | Hlt'' | Hgt'' ];
        destruct (BinPos.Pos.compare_spec my mx) as [ Heq''' | Hlt''' | Hgt''' ];
        intros H;
            try reflexivity;
            try discriminate H;
            try (
                now subst;
                    try (now apply irreflexivity in Hlt);
                    try (now apply irreflexivity in Hlt');
                    try (now apply irreflexivity in Hlt'');
                    try (now apply irreflexivity in Hlt''');
                    try (now apply irreflexivity in Hgt);
                    try (now apply irreflexivity in Hgt');
                    try (now apply irreflexivity in Hgt'');
                    try (now apply irreflexivity in Hgt''');
                    try (now apply asymmetry in Hlt);
                    try (now apply asymmetry in Hlt');
                    try (now apply asymmetry in Hlt'');
                    try (now apply asymmetry in Hlt''');
                    try (now apply asymmetry in Hgt);
                    try (now apply asymmetry in Hgt');
                    try (now apply asymmetry in Hgt'');
                    try (now apply asymmetry in Hgt''')
            ).
    Defined.

    Definition compare_lt_trans (x y z : float) :
        SFcompare (Prim2SF x) (Prim2SF y) = Some Lt ->
        SFcompare (Prim2SF y) (Prim2SF z) = Some Lt ->
        SFcompare (Prim2SF x) (Prim2SF z) = Some Lt.
    Proof.
        destruct (Prim2SF x) as [ sx | sx | | sx mx ex ] eqn:Heqx;
        destruct (Prim2SF y) as [ sy | sy | | sy my ey ] eqn:Heqy;
        destruct (Prim2SF z) as [ sz | sz | | sz mz ez ] eqn:Heqz;
        try (destruct sx);
        try (destruct sy);
        try (destruct sz);
        simpl;
            try (now intros H1 H2; try discriminate H1; discriminate H2);
            try reflexivity;
        replace (BinPos.Pos.compare_cont Eq) with (BinPos.Pos.compare);
            try reflexivity;
        destruct (BinInt.Z.compare_spec ex ey) as [ Heq | Hlt | Hgt ];
        destruct (BinInt.Z.compare_spec ey ez) as [ Heq' | Hlt' | Hgt' ];
        destruct (BinInt.Z.compare_spec ex ez) as [ Heq'' | Hlt'' | Hgt'' ];
        destruct (BinPos.Pos.compare_spec mx my) as [ Heq''' | Hlt''' | Hgt''' ];
        destruct (BinPos.Pos.compare_spec my mz) as [ Heq'''' | Hlt'''' | Hgt'''' ];
        destruct (BinPos.Pos.compare_spec mx mz) as [ Heq''''' | Hlt''''' | Hgt''''' ];
        intros H;
            try reflexivity;
            try discriminate H;
            try (
                now subst;
                    try (now apply irreflexivity in Hlt);
                    try (now apply irreflexivity in Hlt');
                    try (now apply irreflexivity in Hlt'');
                    try (now apply irreflexivity in Hlt''');
                    try (now apply irreflexivity in Hlt'''');
                    try (now apply irreflexivity in Hlt''''');
                    try (now apply irreflexivity in Hgt);
                    try (now apply irreflexivity in Hgt');
                    try (now apply irreflexivity in Hgt'');
                    try (now apply irreflexivity in Hgt''');
                    try (now apply irreflexivity in Hgt'''');
                    try (now apply irreflexivity in Hgt''''');
                    try (now apply asymmetry in Hlt);
                    try (now apply asymmetry in Hlt');
                    try (now apply asymmetry in Hlt'');
                    try (now apply asymmetry in Hlt''');
                    try (now apply asymmetry in Hlt'''');
                    try (now apply asymmetry in Hlt''''');
                    try (now apply asymmetry in Hgt);
                    try (now apply asymmetry in Hgt');
                    try (now apply asymmetry in Hgt'');
                    try (now apply asymmetry in Hgt''');
                    try (now apply asymmetry in Hgt'''');
                    try (now apply asymmetry in Hgt''''');
                    try (now apply transitivity with (x := ez), asymmetry in Hlt);
                    try (now apply transitivity with (x := ez), asymmetry in Hgt);
                    try (now apply transitivity with (x := mz), asymmetry in Hlt''');
                    try (now apply transitivity with (x := mz), asymmetry in Hgt''')
            ).
    Defined.

    Definition leb_trans (x y z : float_std) :
        leb x y = true -> leb y z = true -> leb x z = true.
    Proof.
        unfold leb; rewrite 3 leb_spec;
        unfold SFleb;
        destruct (compare_wd x y) as [[ H1 | H1 ] | H1 ];
        destruct (compare_wd y z) as [[ H2 | H2 ] | H2 ];
        destruct (compare_wd x z) as [[ H3 | H3 ] | H3 ];
        rewrite H1, H2, H3;
        intros H4 H5;
            try reflexivity;
            try discriminate H4;
            try discriminate H5;
            try (
                now eapply compare_eq_1 in H1; rewrite H1 in H2;
                rewrite H2 in H3; discriminate H3);
            try (
                now eapply compare_eq_2 in H2; rewrite H2 in H3;
                rewrite H1 in H3; discriminate H3);
            apply compare_lt_trans with (z := proj1_sig z) in H1;
                [ rewrite H1 in H3; discriminate H3
                | apply H2 ].
    Defined.

End FloatTTLB.

Module FloatOT : OrderedType
    with Definition t := float_std :=
    TTLB_to_OTF FloatTTLB.

Module FloatOTF : OrderedTypeFull
    with Definition t := float_std :=
    OT_to_Full FloatOT.

Module FloatSet : Sets
    with Module E := FloatOT :=
    MSetList.Make FloatOT.

Module FloatSetProperties := OrdProperties FloatSet.


(* List utils *)

Section ListInit.

    Context {A : Type} (f : nat -> A).

    Fixpoint init_aux (n : nat) (acc : list A) : list A :=
        match n with
        | 0 => acc
        | S n' => init_aux n' (f n' :: acc)
        end.

    Definition init (n : nat) :=
        init_aux n [].

    Lemma init_aux_length : forall (n : nat) (acc : list A),
        length (init_aux n acc) = n + length acc.
    Proof.
        induction n as [| n' IH ]; intros; simpl;
            try reflexivity;
        rewrite IH; simpl; lia.
    Qed.

    Theorem init_length : forall (n : nat),
        length (init n) = n.
    Proof. now intros; unfold init; rewrite init_aux_length. Qed.

    Theorem init_0 :
        init 0 = [].
    Proof. reflexivity. Qed.

    Lemma init_aux_acc : forall (n : nat) (acc : list A),
        init_aux n acc = init_aux n [] ++ acc.
    Proof.
        induction n as [| n' IH ]; intros; simpl;
            try reflexivity;
        now rewrite IH, IH with (acc := [ f n' ]), <- app_assoc.
    Qed.

    Theorem init_S : forall (n : nat),
        init (S n) = init n ++ [ f n ].
    Proof.
        unfold init; induction n as [| n' IH ]; intros;
            try reflexivity;
        rewrite IH, <- app_assoc; simpl;
        now rewrite init_aux_acc.
    Qed.

    Theorem init_nth_error_None : forall (n i : nat),
        n <= i ->
        nth_error (init n) i = None.
    Proof. now intros; rewrite nth_error_None, init_length. Qed.

    Theorem init_nth_error_Some : forall (n i : nat),
        i < n ->
        nth_error (init n) i = Some (f i).
    Proof.
        induction n as [| n' IH ]; intros i H; inversion H;
        rewrite init_S.
        -   rewrite nth_error_app2, init_length, Nat.sub_diag;
            now rewrite ? init_length.
        -   rewrite nth_error_app1, IH;
            now rewrite ? init_length.
    Qed.

End ListInit.


(* Non-empty lists *)

Section NonEmptyList.

    Variable (A : Type).

    Inductive nelist :=
    | necons (x : A) (l : list A).

End NonEmptyList.

Arguments necons {A}.


(* Finite types *)

Section Fin.

    Inductive fin : nat -> Type :=
    | F1 {n : nat} : fin (S n)
    | FS {n : nat} : fin n -> fin (S n).

    Fixpoint to_nat {n : nat} (p : fin n) : nat :=
        match p with
        | F1 => 0
        | FS p => S (to_nat p)
        end.

    Definition to_fin : forall {n : nat} (i : nat), fin n + { ~ i < n }.
        refine (fix to_fin {n : nat} {struct n} :=
            match n return forall (i : nat), fin n + { ~ i < n } with
            | 0 => fun i => inright _
            | S n => fun i =>
                match i return fin (S n) + { ~ i < S n } with
                | 0 => inleft F1
                | S i =>
                    match to_fin i with
                    | inleft p => inleft (FS p)
                    | inright _ => inright _
                    end
                end
            end
        );
        lia.
    Defined.

    Theorem to_nat_lt {n : nat} :
        forall (p : fin n), to_nat p < n.
    Proof.
        induction p;
        [   apply Nat.lt_0_succ
        |   simpl; now apply -> Nat.succ_lt_mono ].
    Qed.

    Theorem to_nat_to_fin {n : nat} :
        forall (p : fin n), to_fin (to_nat p) = inleft p.
    Proof.
        induction p as [| n p IH ]; try reflexivity;
        simpl; now rewrite IH.
    Qed.

    Theorem to_fin_to_nat {n : nat} :
        forall (i : nat) (p : fin n), to_fin i = inleft p -> to_nat p = i.
    Proof.
        induction n as [| n IH ]; intros i p H; try (now inversion p);
        dependent destruction p.
        -   destruct i; try reflexivity;
            simpl in H; destruct (@to_fin n i); inversion H.
        -   destruct i; try (now inversion H);
            simpl in H; destruct (@to_fin n i) eqn:Heqi;
                try (now inversion H);
            simpl; f_equal; apply IH; now inversion H.
    Qed.

    Theorem to_nat_inj {n : nat} :
        forall (m p : fin n), to_nat m = to_nat p -> m = p.
    Proof.
        intros m p H; cut (@inleft (fin n) (~ to_nat m < n) m = inleft p);
        [   intro H'; now inversion H'
        |   now rewrite <- to_nat_to_fin, H, -> to_nat_to_fin ].
    Qed.

    Theorem to_fin_lt {n : nat} :
        forall (i : nat) (p : fin n), to_fin i = inleft p -> i < n.
    Proof.
        intros i p H; apply to_fin_to_nat in H;
        rewrite <- H; now apply to_nat_lt.
    Qed.


    Definition to_nat' {n : nat} (p : fin n) : { i : nat | i < n } :=
        exist _ (to_nat p) (to_nat_lt p).

    Definition to_fin' {n : nat} : { i : nat | i < n } -> fin n.
        refine (fun '(exist _ i q) =>
            match @to_fin n i with
            | inleft p => p
            | inright _ => _
            end
        );
        lia.
    Defined.

    Theorem to_fin_pi' {n : nat} :
        forall (i : nat) (p q : i < n), to_fin' (exist _ i p) = to_fin' (exist _ i q).
    Proof.
        intros i; simpl; destruct (to_fin i);
        try reflexivity; contradiction.
    Qed.

    Theorem to_nat_to_fin' {n : nat} :
        forall (p : fin n), to_fin' (to_nat' p) = p.
    Proof. intro p; unfold to_nat', to_fin'; now rewrite to_nat_to_fin. Qed.

    Theorem to_fin_to_nat' {n : nat} :
        forall (i : nat) (q : i < n), to_nat (to_fin' (exist _ i q)) = i.
    Proof.
        intros i q; destruct (@to_fin n i) as [ p |] eqn:Heqi; try lia;
        cut (to_nat p = i); try (now apply to_fin_to_nat);
        intro E; rewrite <- E; simpl; now rewrite Heqi.
    Qed.


    Fixpoint lift {n : nat} (i : fin n) : fin (S n) :=
        match i with
        | F1 => F1
        | FS i => FS (lift i)
        end.

    Fixpoint liftn {p : nat} (n : nat) : fin p -> fin (n + p) :=
        match n return fin p -> fin (n + p) with
        | 0 => fun i => i
        | S n => fun i => lift (liftn n i)
        end.

End Fin.

Module Type FinSig.
    Parameter n : nat.
End FinSig.

Module FinOT (S : FinSig) : UsualOrderedType
    with Definition t := fin S.n.

    Definition t := fin S.n.
    Definition eq := @Logic.eq t.
    Definition lt := fun m p => (@to_nat S.n m < @to_nat S.n p)%nat.
    Definition compare := fun m p => @to_nat S.n m ?= @to_nat S.n p.

    Program Instance eq_equiv : Equivalence eq.

    Program Instance lt_irreflexive : Irreflexive lt.
    Next Obligation. unfold lt; intros p H; lia. Qed.

    Program Instance lt_transitive : Transitive lt.
    Next Obligation. unfold lt in *; lia. Qed.

    Program Instance lt_strorder : StrictOrder lt.

    Program Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
    Next Obligation. unfold lt; intros m m' Hm p p' Hp; now rewrite Hm, Hp. Qed.


    Theorem compare_spec (m p : fin S.n) : CompareSpec (m = p) (lt m p) (lt p m) (compare m p).
    Proof.
        unfold lt, compare;
        assert (H := PeanoNat.Nat.compare_spec (to_nat m) (to_nat p));
        inversion H as [HEq | HLt | HGt]; clear H; constructor;
        try assumption; now apply to_nat_inj.
    Qed.

    Definition eq_dec (m p : fin S.n) : { m = p } + { m <> p }.
    Proof.
        destruct (PeanoNat.Nat.eq_dec (to_nat m) (to_nat p)) as [HEq | HNeq].
        -   left; now apply to_nat_inj.
        -   right; intro abs; now rewrite abs in HNeq.
    Qed.

End FinOT.

Module FinOTF (S : FinSig) : UsualOrderedTypeFull
    with Definition t := fin S.n.
    Module FOT := FinOT S.
    #[warnings="-parsing"] Include OT_to_Full FOT.
End FinOTF.

Module FinSet (S : FinSig) <: Sets
    with Definition E.t := fin S.n
    with Definition E.eq := @Logic.eq (fin S.n).
    Module X := FinOT S.
    Include MSetList.Make X.


    Local Program Fixpoint all_below (n : nat) : t + { ~ n <= S.n } :=
        match n with
        | 0 => inleft empty
        | S n =>
            match to_fin n with
            | inleft p =>
                match all_below n with
                | inleft s => inleft (add p s)
                | inright _ => inright _
                end
            | inright _ => inright _
            end
        end.
    Solve All Obligations with lia.

    Lemma In_all_below : forall (n : nat), n <= S.n ->
        exists (s : t), all_below n = inleft s /\
            forall (i : elt), to_nat i < n -> In i s.
    Proof.
        induction n as [| n IH ]; intros Hn.
        -   exists empty; split; try reflexivity;
            intros i H; inversion H.
        -   destruct IH as (s & H1 & H2); try lia;
            destruct (@to_fin S.n n) as [p |] eqn:Heqn; try lia;
            exists (add p s); split;
                try (simpl; now rewrite Heqn, H1);
            intros i Hi; inversion Hi; apply add_spec;
                try (right; now apply H2);
            left; apply to_nat_inj; apply to_fin_to_nat in Heqn; lia.
    Qed.

    Program Definition all :=
        match all_below S.n with
        | inleft t => t
        | inright _ => _
        end.
    Solve All Obligations with lia.

    Theorem In_all : forall (i : elt), In i all.
    Proof.
        intros i; unfold all;
        destruct (In_all_below S.n (le_n S.n)) as (s & H1 & H2);
        rewrite H1; apply H2, to_nat_lt.
    Qed.

    Theorem all_spec : forall (i : elt), In i all <-> True.
    Proof. intros; split; try auto; intro; apply In_all. Qed.


    Definition compl (s : t) : t := diff all s.

    Theorem In_compl : forall (s : t) (i : elt), In i (compl s) <-> ~ In i s.
    Proof. intros s i; unfold compl; rewrite diff_spec, all_spec; tauto. Qed.

    Global Instance compl_compat : Proper (Equal ==> Equal) compl.
    Proof.
        intros s1 s2 HEs x; rewrite 2 In_compl;
        split; intros H abs; now apply H, HEs.
    Qed.

End FinSet.

Module FinSetProperties (S : FinSig).
    Module FOT := FinOTF S.
    Module FS := FinSet S.
    Module P := OrdProperties FS.
    Module P' := MSets.MSetFacts.WFactsOn FOT FS.
    Import P P.P P'.

    Import FS.

    Theorem compl_compl : forall (s : t), Equal (compl (compl s)) s.
    Proof.
        intros s x; split; intro H.
        -   rewrite 2 In_compl in H; now destruct (In_dec x s).
        -   now rewrite 2 In_compl.
    Qed.

    Theorem Subset_compl :
        forall (s1 s2 : t),
            Subset s1 s2 <-> Subset (compl s2) (compl s1).
    Proof.
        intros s1 s2; split; intros HS x Hx.
        -   apply In_compl; intro abs;
            apply In_compl in Hx; apply Hx, HS, abs.
        -   destruct (In_dec x s2) as [| HN ]; try trivial.
            apply In_compl, HS, In_compl in HN; contradiction.
    Qed.

End FinSetProperties.

(* a reflexivity proof in Feature breaks if I remove this?? *)
Export StringSetMoreProperties.