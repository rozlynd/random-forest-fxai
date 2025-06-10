Require Import List String Orders MSets Floats PrimFloat ZArith Arith.
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
Export StringSetProperties StringSetProperties.P.


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
Export FloatSetProperties FloatSetProperties.P.


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