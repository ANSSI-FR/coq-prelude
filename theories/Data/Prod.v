From Coq Require Import Equivalence.
From Base Require Export Init Equality.

Inductive prod_equal `{EquP a, EquP b} : a * b -> a * b -> Prop :=
| prod_term_equal (x x' : a) (y y' : b) (equ1 : x === x') (equ2 : y === y')
  : prod_equal (x, y) (x', y').

Lemma prod_equal_refl `{EquP' a, EquP' b} (x : a * b) : prod_equal x x.

Proof.
  now destruct x.
Qed.

Lemma prod_equal_sym `{EquP' a, EquP' b} (x y : a * b) (equ : prod_equal x y)
  : prod_equal y x.

Proof.
  inversion equ; subst.
  now constructor.
Qed.

Lemma prod_equal_trans `{EquP' a, EquP' b} (x y z : a * b)
    (equ1 : prod_equal x y) (equ2 : prod_equal y z)
  : prod_equal x z.

Proof.
  inversion equ1; subst.
  inversion equ2; subst.
  constructor.
  + transitivity x'; auto.
  + transitivity y'; eauto.
Qed.

#[refine]
Instance prod_equal_Equivalence `(EquP' a, EquP' b)
  : Equivalence (@prod_equal a _ b _) := {}.

Proof.
  + unfold Reflexive.
    apply prod_equal_refl.
  + unfold Symmetric.
    apply prod_equal_sym.
  + unfold Transitive.
    apply prod_equal_trans.
Qed.

Instance prod_EquP `(EquP a, EquP b) : EquP (a * b) :=
  { equal := prod_equal }.

Instance prod_EquP' `(EquP' a, EquP' b) : EquP' (a * b) := {}.

Definition prod_equalb `{Equ a, Equ b} (x y : a * b) : bool :=
  (fst x == fst y) && (snd x == snd y).

Instance prod_Equ `(Equ a, Equ b) : Equ (a * b) :=
  { equalb := prod_equalb }.

#[refine]
Instance prod_Equ' `(Equ' a, Equ' b) : Equ' (a * b) := {}.

Proof.
  intros x y.
  destruct x; destruct y.
  split; intros equ.
  + inversion equ; subst.
    cbn.
    apply Bool.andb_true_iff.
    split; cbn -[equalb].
    ++ now rewrite <- equal_equalb_equiv; [| apply H2].
    ++ now rewrite <- equal_equalb_equiv; [| apply H6].
  + apply Bool.andb_true_iff in equ.
    destruct equ as [ equ1 equ2 ]; unfold fst, snd in *.
    rewrite <- equal_equalb_equiv in equ1; [| apply H2].
    rewrite <- equal_equalb_equiv in equ2; [| apply H6].
    now constructor.
Qed.

Instance fst_Proper (a b : Type) : EquMorphism (@fst a b).

Proof.
  add_morphism_tactic.
  intros [ x x' ] [ y y' ] equ.
  now inversion equ; subst.
Qed.

Instance snd_Proper (a b : Type) : EquMorphism (@snd a b).

Proof.
  add_morphism_tactic.
  intros [ x x' ] [ y y' ] equ.
  now inversion equ; subst.
Qed.

Module ProdExtraction.
  Extract Inductive prod => "( * )" [ "" ].
End ProdExtraction.
