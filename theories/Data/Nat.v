Require Import Coq.Program.Tactics.

Class Nat a :=
  { zero: a
  ; succ: a -> a
  ; succ_injective: forall (n m: a), succ n = succ m -> n = m
  ; succ_not_zero: forall (n: a), succ n <> zero
  ; peano_rect: forall (P:   a -> Prop),
      P zero
      -> (forall n, P n -> P (succ n))
      -> (forall (n:   a), P n)
  }.

Ltac nat_induction p := induction p using peano_rect.

Lemma succ_n_neq_n
      {a} `{Nat a}
      (n: a)
  : succ n <> n.
Proof.
  nat_induction n.
  + apply succ_not_zero.
  + intros Hfalse.
    now apply succ_injective in Hfalse.
Qed.

Inductive le
          {a} `{Nat a}
          (n: a)
  : a -> Prop :=
| le_refl: le n n
| le_succ (m: a)
  : le n m -> le n (succ m).

Notation "x <= y" := (le x y): nat_scope.

Open Scope nat_scope.

Lemma le_n_succ_n
      {a} `{Nat a}
      (n: a)
  : n <= (succ n).
Proof.
  apply le_succ.
  apply le_refl.
Qed.

Lemma le_trans_succ
      {a} `{Nat a}
      (r s: a)
  : succ r <= s -> r <= s.
Proof.
  intros Hle.
  induction Hle.
  + apply le_n_succ_n.
  + apply le_succ.
    apply IHHle.
Qed.

Lemma not_le_succ_n_zero
      {a} `{Nat a}
      (n: a)
  : ~ succ n <= zero.
Proof.
  intros Hle.
  inversion Hle.
  + now apply succ_not_zero in H1.
  + now apply succ_not_zero in H0.
Qed.

Lemma le_succ_n_succ_m_le_n_m
      {a} `{Nat a}
      (n m: a)
  : succ n <= succ m -> n <= m.
Proof.
  intros Hle.
  inversion Hle; subst.
  + apply succ_injective in H1; subst.
    apply le_refl.
  + apply succ_injective in H0; subst.
    now apply le_trans_succ in H1.
Qed.

Lemma not_le_succ_n_n
      {a} `{Nat a}
      (n: a)
  : ~ succ n <= n.
Proof.
  nat_induction n.
  + apply not_le_succ_n_zero.
  + intros Hfalse.
    now apply le_succ_n_succ_m_le_n_m in Hfalse.
Qed.

Lemma le_trans
      {a} `{Nat a}
      (r s t: a)
  : r <= s -> s <= t -> r <= t.
Proof.
  intros H1.
  revert t.
  induction H1.
  + auto.
  + intros t H2.
    apply IHle.
    now apply le_trans_succ in H2.
Qed.

Definition lt
           {a} `{Nat a}
           (n m:  a)
  : Prop :=
  le (succ n) m.

Notation "x < y" := (lt x y): nat_scope.

Lemma lt_not_refl
      {a} `{Nat a}
      (n: a)
  : ~ n < n.
Proof.
  intro Hfalse.
  unfold lt in Hfalse.
  now apply not_le_succ_n_n in Hfalse.
Qed.

Program Instance nat_Nat
  : Nat nat :=
  { zero := O
  ; succ := S
  ; peano_rect := nat_rect
  }.

Require Coq.NArith.NArith.

Instance N_Nat
  : Nat BinNums.N :=
  { zero := BinNat.N.of_nat O
  ; succ := BinNat.N.succ
  ; peano_rect := BinNat.N.peano_rect
  ; succ_injective := BinNat.N.succ_inj
  ; succ_not_zero := BinNat.N.neq_succ_0
  }.