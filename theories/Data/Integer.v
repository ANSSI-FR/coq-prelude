Set Implicit Arguments.

Require Import Coq.Setoids.Setoid.

Require Import Prelude.Control.
Require Import Prelude.Control.Option.
Require Import Prelude.Equality.
Require Import Prelude.Tactics.

(** From [Prelude], we reuse the [option] monad implementation and
    the [Equality] typeclass.
 *)
Local Open Scope prelude_scope.

Require Import Coq.ZArith.ZArith.
Local Open Scope Z_scope.

(** The [size] of a bounded (unsigned or signed) integer is the number
    of bits used to represent it in memory. *)
Definition size := { n: Z | 0 < n }.

(* begin hide *)
Remark Z_neg_not_lt_0
       (p:  positive)
  : ~ (0 < Z.neg p).
Proof.
  intros F.
  apply Z.lt_asymm in F.
  now assert (Z.neg p < 0) by apply Pos2Z.neg_is_neg.
Qed.
(* end hide *)

Module unsigned.
Section def.
  Variable n: size.

  #[program]
  Definition max := 2^n.

  Remark max_lt_0: 0 < max.
  Proof.
    unfold max.
    induction n as [n' Hn]; cbn in *.
    induction n'.
    + inversion Hn.
    + apply Z.pow_pos_nonneg.
      ++ constructor.
      ++ apply Pos2Z.is_nonneg.
    + cbn.
      now apply Z_neg_not_lt_0 in Hn.
  Qed.

  Definition t := { x: Z | 0 <= x < max }.

End def.
End unsigned.

Module signed.
Section def.
  Variable n: size.

  #[program]
  Definition min := -2^(n-1).

  #[program]
  Definition max := 2^(n-1).

  Remark max_min_eq: max = - min.
  Proof.
    unfold min, max.
    now rewrite Z.opp_involutive.
  Qed.

  Definition t := { x: Z | min <= x < max }.
End def.
End signed.

#[program]
Remark max_signed_min_signed
       (n: size)
  : signed.max n = - signed.min n.
Proof.
  unfold signed.min, signed.max.
  now rewrite Z.opp_involutive.
Qed.

#[program]
Remark min_signed_max_signed
       (n: size)
  : signed.min n = - signed.max n.
Proof.
  reflexivity.
Qed.

Remark max_signed_lt_max_unsigned n
  : signed.max n < unsigned.max n.
Proof.
  unfold signed.max, unsigned.max.
  apply Z.pow_lt_mono_r.
  + apply Z.lt_1_2.
  + induction n as [n Hn].
    now apply Z.lt_le_incl.
  + now apply Z.lt_sub_pos.
Qed.

Remark max_signed_lt_0 n
  : 0 < signed.max n.
Proof.
  induction n as [n Hn]; cbn in *.
  induction n.
  + inversion Hn.
  + unfold unsigned.max.
    apply Z.pow_pos_nonneg.
    ++ constructor.
    ++ unfold proj1_sig.
       apply Zlt_0_le_0_pred in Hn.
       now rewrite <- Z.sub_1_r in Hn.
  + cbn.
    now apply Z_neg_not_lt_0 in Hn.
Qed.

Remark min_signed_lt_0 n
  : signed.min n < 0.
Proof.
  rewrite min_signed_max_signed.
  apply Z.opp_neg_pos.
  apply max_signed_lt_0.
Qed.

#[program]
Remark max_signed_max_unsigned
       (n: size)
  : unsigned.max n = 2 * signed.max n.
Proof.
  induction n as [n Hn].
  unfold signed.max, unsigned.max, proj1_sig.
  rewrite <- Z.pow_succ_r.
  + rewrite Z.sub_1_r.
    now rewrite Z.succ_pred.
  + now apply Zlt_0_le_0_pred.
Qed.

#[program]
Definition box n x
  : unsigned.t n :=
  x mod 2^n.
Next Obligation.
  apply Z.mod_pos_bound.
  apply unsigned.max_lt_0.
Defined.

Definition unbox
           {n: size}
           (x: unsigned.t n)
  : Z :=
  proj1_sig x.

Add Parametric Morphism
    (n: size)
  : (@unbox n)
    with signature (@equal _ _) ==> eq
      as unbox_is_morphism.
Proof.
  now intros [x Hx] [y Hy] H.
Qed.

Lemma unbox_box_eq
      {n: size}
      (x: unsigned.t n)
  : box n (unbox x) == x.
Proof.
  induction x as [x Hx].
  now apply Z.mod_small.
Qed.

#[program]
Definition unsigned_to_signed
           {n:  size}
           (x:  unsigned.t n)
  : signed.t n :=
  if Z_lt_ge_dec x (signed.max n)
  then x
  else Z.double (signed.min n) + x.
Next Obligation.
  induction x as [x [Hmin Hmax]].
  cbn in *.
  split.
  + transitivity 0.
    ++ apply Z.opp_nonpos_nonneg.
       apply Z.pow_nonneg.
       apply Z.le_0_2.
    ++ exact Hmin.
  + exact H.
Defined.
Next Obligation.
  induction x as [x [Hmin Hmax]].
  cbn in *.
  rewrite Z.double_spec.
  split.
  + rewrite min_signed_max_signed.
    apply Zplus_le_reg_r with (p:=2 * (signed.max n)).
    rewrite <- Z.mul_opp_comm.
    rewrite <- Z.add_assoc.
    rewrite (Z.add_comm x ).
    rewrite Z.add_assoc.
    rewrite <- Z.mul_add_distr_r.
    rewrite Z.add_opp_diag_l.
    rewrite Z.mul_0_l.
    rewrite Z.add_0_l.
    rewrite Z.opp_eq_mul_m1.
    rewrite Z.mul_comm.
    rewrite <- Z.mul_add_distr_r.
    assert (R: - 1 + 2 = 1) by reflexivity.
    rewrite R; clear R.
    rewrite Z.mul_1_l.
    now apply Z.ge_le.
  + rewrite min_signed_max_signed.
    rewrite <- Z.mul_opp_comm.
    rewrite Z.add_comm.
    rewrite Z.mul_opp_l.
    rewrite Z.add_opp_r.
    apply Zplus_lt_reg_r with (p:=2 * (signed.max n)).
    rewrite Z.sub_add.
    rewrite <- max_signed_max_unsigned.
    transitivity (unsigned.max n).
    ++ apply Hmax.
    ++ apply Z.lt_add_pos_l.
       apply max_signed_lt_0.
Defined.

Add Parametric Morphism
    (n: size)
  : (@unsigned_to_signed n)
    with signature (@equal _ _) ==> (@equal _ _)
      as unsigned_to_signed_is_morphism.
Proof.
  intros [x Hx] [y Hy] H.
  unfold unsigned_to_signed.
  destruct Z_lt_ge_dec as [H1|H2]; destruct Z_lt_ge_dec as [H3|H4]; auto; cbn.
  + (* absurd case *)
    rewrite <- H in H4.
    apply Zlt_not_le in H1.
    now apply Z.ge_le in H4.
  + (* absurd case *)
    rewrite <- H in H3.
    apply Zlt_not_le in H3.
    now apply Z.ge_le in H2.
  + cbn in H.
    rewrite H.
    reflexivity.
Qed.

#[program]
Definition signed_to_unsigned
           {n:  size}
           (x:  signed.t n)
  : unsigned.t n :=
  if Z_lt_ge_dec x 0
  then x + Z.double (signed.max n)
  else x.
Next Obligation.
  induction x as [x [Hmin Hmax]]; cbn in *.
  split.
  + rewrite Z.double_spec.
    rewrite max_signed_min_signed.
    rewrite Z.mul_opp_r.
    apply Zplus_le_reg_r with (p:=2 * (signed.min n)).
    rewrite Z.add_opp_r.
    rewrite Z.sub_add.
    rewrite Z.add_0_l.
    transitivity (signed.min n).
    ++ rewrite Z.mul_comm.
       apply Z.le_mul_diag_l.
       +++ apply min_signed_lt_0.
       +++ apply Z.le_succ_diag_r.
    ++ exact Hmin.
  + rewrite Z.double_spec.
    rewrite max_signed_max_unsigned.
    apply Zplus_lt_reg_r with (p:=-(2)*(signed.max n)).
    rewrite <- Z.add_assoc.
    rewrite Z.mul_opp_l.
    repeat rewrite Z.add_opp_diag_r.
    now rewrite Z.add_0_r.
Defined.
Next Obligation.
  induction x as [x [Hmin Hmax]].
  cbn in *.
  split.
  + now apply Z.ge_le.
  + transitivity (signed.max n).
    ++ exact Hmax.
    ++ apply max_signed_lt_max_unsigned.
Defined.

Add Parametric Morphism
    (n: size)
  : (@signed_to_unsigned n)
    with signature (@equal _ _) ==> (@equal _ _)
      as signed_to_unsigned_is_morphism.
Proof.
  intros [x Hx] [y Hy] H.
  unfold signed_to_unsigned.
  unfold proj1_sig in *.
  destruct Z_lt_ge_dec as [H1|H2]; destruct Z_lt_ge_dec as [H3|H4]; auto.
  + cbn in *.
    rewrite H.
    reflexivity.
  + (* absurd case *)
    cbn in *.
    rewrite <- H in H4.
    apply Zlt_not_le in H1.
    now apply Z.ge_le in H4.
  + (* absurd case *)
    cbn in *.
    rewrite <- H in H3.
    apply Zlt_not_le in H3.
    now apply Z.ge_le in H2.
Qed.

Lemma signed_to_unsigned_unsigned_to_signed
      {n: size}
      (x: unsigned.t n)
  : signed_to_unsigned (unsigned_to_signed x) == x.
Proof.
  induction x as [x [Hmin Hmax]].
  unfold unsigned_to_signed.
  destruct Z_lt_ge_dec as [H1|H2]; unfold signed_to_unsigned.
  + cbn in H1.
    destruct Z_lt_ge_dec as [H3|H4]; unfold proj1_sig in *.
    ++ cbn in *.
       apply Zlt_not_le in H3.
       now apply H3 in Hmin.
    ++ reflexivity.
  + cbn in H2.
    destruct Z_lt_ge_dec as [H3|H4]; unfold proj1_sig in *.
    ++ cbn in *.
       rewrite min_signed_max_signed.
       rewrite Z.double_spec.
       rewrite Z.add_comm.
       rewrite Z.add_assoc.
       rewrite Z.double_spec.
       rewrite Z.mul_opp_r.
       now rewrite Z.add_opp_diag_r.
    ++ cbn in *.
       rewrite Z.double_spec in *.
       rewrite min_signed_max_signed in *.
       rewrite Z.mul_opp_r in *.
       rewrite <- max_signed_max_unsigned in *.
       apply Z.ge_le in H4.
       apply Z.ge_le in H2.
       apply Zplus_le_compat_r with (p:=unsigned.max n) in H4.
       rewrite Z.add_0_l in H4.
       rewrite Z.add_comm in H4.
       rewrite Z.add_assoc in H4.
       rewrite Z.add_opp_diag_r in H4.
       now apply Zlt_not_le in H4.
Qed.

Lemma unsigned_to_signed_signed_to_unsigned
      {n: size}
      (x: signed.t n)
  : unsigned_to_signed (signed_to_unsigned x) == x.
Proof.
  induction x as [x [Hmin Hmax]].
  unfold signed_to_unsigned.
  destruct Z_lt_ge_dec as [H1|H2]; unfold unsigned_to_signed.
  + cbn in H1.
    destruct Z_lt_ge_dec as [H3|H4]; unfold proj1_sig in *.
    ++ cbn in *.
       rewrite Z.double_spec in *.
       rewrite min_signed_max_signed in *.
       apply Zplus_lt_compat_r with (p:=- (2 * (signed.max n))) in H3.
       rewrite <- Z.add_assoc in H3.
       rewrite Z.add_opp_diag_r in H3.
       rewrite Z.add_0_r in H3.
       rewrite <- Z.mul_opp_l in H3.
       rewrite <- (Z.mul_1_l (signed.max n)) in H3 at 1.
       rewrite <- Z.mul_add_distr_r in H3.
       assert (R: 1 + - (2) = - 1) by reflexivity; rewrite R in H3; clear R.
       rewrite Z.mul_comm in H3.
       rewrite <- Z.opp_eq_mul_m1 in H3.
       now apply Zlt_not_le in H3.
    ++ cbn in *.
       rewrite min_signed_max_signed.
       rewrite Z.double_spec.
       rewrite Z.add_comm.
       rewrite Z.double_spec.
       rewrite Z.mul_opp_r.
       rewrite <- Z.add_assoc.
       rewrite Z.add_opp_diag_r.
       now rewrite Z.add_0_r.
  + cbn in H2.
    destruct Z_lt_ge_dec as [H3|H4]; unfold proj1_sig in *.
    ++ reflexivity.
    ++ cbn in *.
       apply Z.ge_le in H4.
       now apply Zlt_not_le in H4.
Qed.

#[program]
Definition unsigned_add
           {n:    size}
           (x y:  unsigned.t n)
  : unsigned.t n :=
  box n (x + y).

Add Parametric Morphism
    (n:  size)
  : (@unsigned_add n)
    with signature @equal _ _ ==> @equal _ _ ==> @equal _ _
      as unsigned_add_is_morphism.
Proof.
  intros [x Hx] [x' Hx'] H [y Hy] [y' Hy'] H'.
  cbn in *.
  now subst.
Qed.

Lemma unsigned_add_comm
      {n: size}
      (x y: unsigned.t n)
  : unsigned_add x y = unsigned_add y x.
Proof.
  unfold unsigned_add.
  rewrite Z.add_comm.
  reflexivity.
Qed.

Lemma unsigned_add_assoc
      {n:      size}
      (x y z:  unsigned.t n)
  : unsigned_add x (unsigned_add y z) == unsigned_add (unsigned_add x y) z.
Proof.
  induction n as [n Hn].
  induction x as [x Hx].
  induction y as [y Hy].
  induction z as [z Hz].
  unfold unsigned_add, box, proj1_sig.
  cbn in *.
  rewrite (Z.add_comm ((x + y) mod _) z) at 1.
  repeat rewrite Zplus_mod_idemp_r.
  assert (R: x + (y + z) = z + (x + y)). {
    rewrite (Z.add_comm z _).
    apply Z.add_assoc.
  }
  now rewrite R.
Qed.

Definition signed_add
           {n: size}
           (x y: signed.t n)
  : signed.t n :=
  unsigned_to_signed (unsigned_add (signed_to_unsigned x) (signed_to_unsigned y)).

Lemma signed_add_unsigned_add
      {n: size}
      (x y: signed.t n)
  : unsigned_add (signed_to_unsigned x) (signed_to_unsigned y)
    == signed_to_unsigned (signed_add x y).
Proof.
  unfold signed_add.
  rewrite signed_to_unsigned_unsigned_to_signed.
  reflexivity.
Qed.

Add Parametric Morphism
    (n:  size)
  : (@signed_add n)
    with signature @equal _ _ ==> @equal _ _ ==> @equal _ _
      as signed_add_is_morphism.
Proof.
  intros x x' H y y' H'.
  unfold signed_add.
  rewrite H.
  now rewrite H'.
Qed.

Lemma signed_add_comm
      {n:  size}
      (x y: signed.t n)
  : signed_add x y = signed_add y x.
Proof.
  unfold signed_add.
  rewrite unsigned_add_comm.
  reflexivity.
Qed.

Lemma signed_add_assoc
      {n:  size}
      (x y z: signed.t n)
  : signed_add x (signed_add y z) == signed_add (signed_add x y) z.
Proof.
  unfold signed_add.
  repeat rewrite signed_to_unsigned_unsigned_to_signed.
  rewrite unsigned_add_assoc.
  reflexivity.
Qed.

#[program]
Definition unsigned_le
           {n:  size}
           (x y:  unsigned.t n)
  : Prop :=
   x <= y.

#[program]
Definition unsigned_le_dec
           {n:  size}
           (x y:  unsigned.t n)
  : { unsigned_le x y } + { ~ unsigned_le x y } :=
  if Z_le_gt_dec x y
  then _
  else _.
Next Obligation.
  now left.
Defined.
Next Obligation.
  right.
  unfold unsigned_le.
  intros F.
  now apply Zle_not_gt in F.
Defined.

Lemma unsigned_le_refl
      {n:  size}
      (x:  unsigned.t n)
  : unsigned_le x x.
Proof.
  unfold unsigned_le.
  reflexivity.
Qed.

Lemma unsigned_le_trans
      {n:  size}
      (x y z:  unsigned.t n)
  : unsigned_le x y
    -> unsigned_le y z
    -> unsigned_le x z.
Proof.
  unfold unsigned_le.
  intros H1 H2.
  now transitivity (proj1_sig y).
Qed.

#[program]
Definition unsigned_lt
           {n:    size}
           (x y:  unsigned.t n)
  : Prop :=
  x < y.

#[program]
Definition unsigned_lt_dec
           {n:  size}
           (x y:  unsigned.t n)
  : { unsigned_lt x y } + { ~ unsigned_lt x y } :=
  if Z_lt_ge_dec x y
  then _
  else _.
Next Obligation.
  now left.
Defined.
Next Obligation.
  right.
  unfold unsigned_lt.
  intros F.
  apply Z.ge_le in H.
  apply Z.lt_gt in F.
  now apply Zle_not_gt in H.
Defined.

#[program]
Definition unsigned_add_protect
           {n:  size}
           (x y:  unsigned.t n)
  : option (unsigned.t n) :=
  let z := x + y in
  if Z_lt_ge_dec z (unsigned.max n)
  then Some (exist _ z _)
  else None.
Next Obligation.
  induction x as [x [Hmin__x Hmax__x]].
  induction y as [y [Hmin__y Hmax__y]].
  cbn in *.
  split.
  + now apply Z.add_nonneg_nonneg.
  + exact H.
Defined.

Lemma unsigned_add_protect_comm
      {n: size}
      (x y: unsigned.t n)
  : unsigned_add_protect x y == unsigned_add_protect y x.
Proof.
  unfold unsigned_add_protect.
  destruct Z_lt_ge_dec.
  + destruct Z_lt_ge_dec.
    ++ constructor.
       cbn.
       apply Z.add_comm.
    ++ apply Z.ge_le in g.
       rewrite Z.add_comm in g.
       apply Zle_not_gt in g.
       pose proof l as l'.
       now apply Z.lt_gt in l'.
  + destruct Z_lt_ge_dec.
    ++ apply Z.ge_le in g.
       rewrite Z.add_comm in g.
       apply Zle_not_gt in g.
       pose proof l as l'.
       now apply Z.lt_gt in l'.
    ++ reflexivity.
Qed.

Lemma unsigned_add_protect_assoc
      {n: size}
      (x y z: unsigned.t n)
  : unsigned_add_protect y z >>= unsigned_add_protect x
    == unsigned_add_protect x y >>= fun r => unsigned_add_protect r z.
Proof.
  induction x as [x [Hmin__x Hmax__x]].
  induction y as [y [Hmin__y Hmay__y]].
  induction z as [z [Hmin__z Hmaz__z]].
  unfold unsigned_add_protect; unfold proj1_sig.
  destruct (Z_lt_ge_dec (y + z) (unsigned.max n)) as [H1|H1]; cbn -[equal].
  + destruct (Z_lt_ge_dec (x + (y + z)) (unsigned.max n)) as [H2|H2]; cbn -[equal].
    ++ destruct (Z_lt_ge_dec (x + y) (unsigned.max n)) as [H3|F]; cbn -[equal].
       +++ destruct (Z_lt_ge_dec (x + y + z) (unsigned.max n)) as [H4|F]; cbn -[equal].
           ++++ constructor.
                unfold proj1_sig.
                apply Z.add_assoc.
           ++++ (* absurd case *)
                rewrite <- Z.add_assoc in F.
                pose proof H2 as H2'.
                apply Z.lt_asymm in H2'.
                apply Z.ge_le in F.
                now apply Zle_not_lt in F.
       +++ (* absurd case *)
           apply Z.ge_le in F.
           apply Zle_not_gt in F.
           contradict F.
           apply Z.lt_gt.
           pose proof H2 as H2'.
           rewrite Z.add_assoc in H2'.
           rewrite <- (Z.add_0_r (unsigned.max n)) in H2'.
           apply Z.add_lt_cases in H2'.
           destruct H2' as [H2'|H2'].
           ++++ auto.
           ++++ now apply Zle_not_lt in H2'.
    ++ destruct (Z_lt_ge_dec (x + y) (unsigned.max n)) as [H3|H3]; cbn -[equal].
       +++ assert (H4: x + y + z >= unsigned.max n) by now rewrite <- Z.add_assoc.
           apply Z.ge_le in H4.
           apply Zle_not_lt in H4.
           destruct (Z_lt_ge_dec (x + y + z) (unsigned.max n)) as [H5|H5].
           ++++ pose proof H5 as H5'.
                now apply H4 in H5'.
           ++++ reflexivity.
       +++ reflexivity.
  + destruct (Z_lt_ge_dec (x + y) (unsigned.max n)) as [H2|H2]; cbn -[equal]; [| reflexivity].
    assert (H3: x + y + z >= unsigned.max n). {
      rewrite <- (Z.add_0_l (unsigned.max n)).
      apply Z.le_ge.
      rewrite <- Z.add_assoc.
      apply Z.add_le_mono; [ auto |].
      now apply Z.ge_le.
    }
    destruct Z_lt_ge_dec as [H4|H4]; [| reflexivity ].
    pose proof H4 as H4'.
    now apply Zlt_not_le in H4'.
Qed.

#[program]
Definition unsigned_mul
           {n: size}
           (x y: unsigned.t n)
  : unsigned.t n :=
  box n (x * y).

Lemma unsigned_mul_comm
      {n: size}
      (x y: unsigned.t n)
  : unsigned_mul x y == unsigned_mul y x.
Proof.
  unfold unsigned_mul.
  now rewrite Z.mul_comm.
Qed.

#[program]
Definition unsigned_mul_protect
           {n: size}
           (x y: unsigned.t n)
  : option (unsigned.t n) :=
  let z := x * y in
  if Z_lt_ge_dec z (unsigned.max n)
  then Some (exist _ z _)
  else None.
Next Obligation.
  induction x as [x [Hmin__x Hmax__x]].
  induction y as [y [Hmin__y Hmax__y]].
  cbn in *.
  split.
  + apply Z.mul_nonneg_nonneg; [exact Hmin__x | exact Hmin__y].
  + exact H.
Qed.

Lemma unsigned_mul_protect_some_trans
      {n:      size}
      (x y z:  unsigned.t n)
  : is_some (unsigned_mul_protect y z >>= unsigned_mul_protect x)
    -> is_some (unsigned_mul_protect x y >>= fun r => unsigned_mul_protect r z)
    -> unsigned_mul_protect y z >>= unsigned_mul_protect x == unsigned_mul_protect x y >>= fun r => unsigned_mul_protect r z.
Proof.
  induction x as [x [Hmin__x Hmax__x]].
  induction y as [y [Hmin__y Hmax__y]].
  induction z as [z [Hmin__z Hmax__z]].
  intros H1 H2.
  inversion H1; inversion H2; subst; cbn -[equal] in *.
  unfold unsigned_mul_protect, proj1_sig in *.
  destruct (Z_lt_ge_dec (y * z) (unsigned.max n)) as [H4|H5]; [| discriminate].
  cbn -[equal] in *.
  destruct (Z_lt_ge_dec (x * (y * z)) (unsigned.max n)); [| discriminate].
  cbn -[equal] in *.
  destruct (Z_lt_ge_dec (x * y) (unsigned.max n)) as [H6|H7]; [| discriminate].
  cbn -[equal] in *.
  destruct (Z_lt_ge_dec (x * y * z) (unsigned.max n)) as [H8|H9]; [| discriminate].
  cbn -[equal] in *.
  constructor.
  unfold proj1_sig.
  cbn in *.
  now rewrite Z.mul_assoc.
Qed.

#[program]
Definition signed_mul
           {n:    size}
           (x y:  signed.t n)
  : signed.t n :=
  unsigned_to_signed (unsigned_mul (signed_to_unsigned x) (signed_to_unsigned y)).
