From Base Require Import Init.
From Coq Require Export Equivalence Setoid Morphisms.

(** The Coq built-in equality [eq] (1) lives inside [Prop], and (2) may
    sometimes be “to strong.” Typically, if a <<Record>> contains a field living
    in [Prop], reasoning about terms equality will eventually imply using an
    axiom (i.e., proof irrelevance). The recent addition of the [SProp] sort
    (that is, [Prop] with built-in proof irrelevance) may solve this particular
    use case, but other exists.

    We first introduce the [Equ] typeclass, which only requires to define a
    computable “equality function”. *)

Class Equ (a : Type) : Type := { equalb : a -> a -> bool }.

(** We introduce two “usual” notations to seamlessly use [equalb]: [==] and
    [!=]. *)

Infix "==" := equalb (at level 70, no associativity) : base_scope.
Notation "x != y" := (negb (equalb x y)) (at level 70, no associativity)
  : base_scope.

(** Then, we introduce [EquProp], which consists in specifying an “equality
    relation” (which lives in [Prop]). *)

Class EquProp (a : Type) : Type := { equal : a -> a -> Prop }.

(** Similarly to [Equ], we attribute two notation to manipulate [equal]: [===]
    and [!==]. *)

Infix "===" := equal (at level 70, no associativity) : base_scope.
Notation "x '!==' y" := (~ equal x y) (at level 70, no associativity)
  : base_scope.

(** We provide a “default” instance for [EquProp], which consists in saying
    that, in the common case, the “equality relation” of any type [a] is
    [eq]. The priority manually assigned to this default instance is high enough
    for any additional instances provided by <<coq-base>> users to be used
    instead. *)

Instance default_EquProp : EquProp a|10000 := { equal := eq }.

(** Finally, we introduce two additional typeclasses: [EquL] and
    [EquPropL]. Following the convention of <<coq-base>>, [EquL] ([EquPropL]
    resp.) specifies the _laws_ [EquL] ([EquProp] resp.) is expected to obey. *)

Class EquPropL (a : Type) `{H : EquProp a} : Type :=
  { equp_is_equivalence :> Equivalence (@equal a H) }.

Class EquL (a : Type) `{EquPropL a, Equ a} : Type :=
  { equal_equalb_equiv : forall (x y : a), x === y <-> x == y = true }.

Arguments equal_equalb_equiv [a _ _ _ _] (x y).

(** Since [EquProp] comes with a so-called “default instance”, we introduce the
    related instance for [EquPropL]. *)

Instance default_EquPropL : EquPropL a|10000 := {}.

(** * [Equ] Morphisms *)

(** Users of <<coq-base>> are encouraged to reason in terms of equalities
    specified by [Equ] and [EquProp] rather than [eq]. In pratice, this can make
    rewriting difficult (a phenomenon called “setoid hell”). To limit the risk
    of running into this issue, we introduce the notion of “[Equ] morphism”.

    A function [f] is an [Equ] morphism if, when [x === y], then [f x === f
    y]. We introduce the “[EquMorphism] typeclass” (in practice, a
    specialization of the [Proper] typeclass). *)

#[local]
Ltac morphism_signature a :=
  match a with
  | ?a -> ?b => exact ((@equal a _) ==> ltac:(morphism_signature b))%signature
  | ?b => exact (@equal b _)
  end.

Ltac equ_morphism a :=
  match type of a with
  | ?t => exact (Proper ltac:(morphism_signature t) a)
  end.

Notation "'EquMorphism' f" :=
  ltac:(equ_morphism f) (at level 200, only parsing) : base_scope.

(** * Ad-hoc Equality for Functions *)

(** Two function are said “equal” when, given the same input, they produce
    “equal” outputs. *)

Instance func_EquProp `(EquProp b) : EquProp (func a b) :=
  { equal := fun f g => forall x, f x === g x }.

(** One could want to provide a slightly different definition of [equal] for
    function, such that for two “equal” term _x_ and _y_, two equal functions
    compute “equal” result. Unfortunately, this is not possible. In particular,
    such relation may not be symetric. A function which is not an [Equ] morphism
    (see previous section) will not be “equal” to itself under this relation. *)

#[refine]
Instance func_EquPropL `(EquPropL b) : EquPropL (func a b) := {}.

Proof.
  constructor.
  + unfold Reflexive.
    now intros.
  + unfold Symmetric.
    intros f g equ x.
    now symmetry.
  + unfold Transitive.
    intros f g h equ1 equ2 x.
    transitivity (g x); [ apply equ1 | apply equ2 ].
Qed.
