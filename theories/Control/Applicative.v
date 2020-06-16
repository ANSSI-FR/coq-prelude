From Base Require Export Functor.

Class Applicative (f : Type -> Type) `{Functor f} : Type :=
  { pure {a} : a -> f a
  ; apply {a b} : f (a -> b) -> f a -> f b
  }.

Arguments pure [f _ _ a] (_).
Arguments apply [f _ _ a b] (_ _).

Notation "f <*> g" := (apply f g) (at level 28, left associativity) : base_scope.

Definition liftA2 {f a b c} `{Applicative f}
    (g : a -> b -> c) (x : f a) (y : f b)
  : f c :=
  map g x <*> y.

Class ApplicativeL (f : Type -> Type) `{FunctorL f, ! Applicative f} : Type :=
  { applicative_identity `{EquPropL a} (v : f a) : pure id <*> v === v
  ; applicative_composition {a b c} `{EquPropL c} (u : f (b -> c)) (v : f (a -> b)) (w : f a)
    : pure compose <*> u <*> v <*> w === u <*> (v <*> w)
  ; applicative_homomorphism {a b} `{EquPropL b} (v : a -> b) (x : a)
    : (pure v) <*> (pure x) === pure (v x)
  ; applicative_interchange {a b} `{EquPropL b} (u : f (a -> b)) (y : a)
    : u <*> (pure y) === (pure (fun z => z y)) <*> u
  ; applicative_pure_map {a b} `{EquPropL b} (g : a -> b) (x : f a)
    : g <$> x === pure g <*> x
  }.

Definition rseq `{Applicative f} {a b} (x : f a) (y : f b) : f b :=
  (id <$ x) <*> y.

Notation "f *> g" := (rseq f g) (at level 28, left associativity) : base_scope.

Definition lseq `{Applicative f} {a b} (x : f a) (y : f b) : f a :=
  liftA2 (fun x y => x) x y.

Notation "f <* g" := (lseq f g) (at level 28, left associativity) : base_scope.
