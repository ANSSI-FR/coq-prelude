From Base Require Export Monad Prod Identity.
From Coq Require Import FunctionalExtensionality.

Class MonadState (s : Type) (m : Type -> Type) :=
  { get : m s
  ; put : s -> m unit
  }.

Definition state_t (s : Type) (m : Type -> Type) (a : Type) := s -> m (a * s).

Definition run_state_t {m s a} (r : state_t s m a) (x : s) : m (a * s) :=
  r x.

Definition eval_state_t {s a} `{Functor m} (r : state_t s m a) (x : s) : m a :=
  fst <$> r x.

Definition exec_state_t {s a} `{Functor m} (r : state_t s m a) (x : s) : m s :=
  snd <$> r x.

Definition state_map {m s} `{Functor m} {a b} (f : a -> b) (r : state_t s m a)
  : state_t s m b :=
  fun x => (fun o => (f (fst o), snd o)) <$> r x.

Instance state_Functor `(Functor m) : Functor (state_t s m) :=
  { map := @state_map m s _ }.

#[refine]
Instance state_Functor' `(Functor' m) : Functor' (state_t s m) := {}.

Proof.
  + intros a Ha Ha' x r.
    cbn.
    unfold state_map.
    unfold id.
    replace (fun o : a * s => (fst o, snd o)) with (@id (a * s)).
    ++ now rewrite functor_identity.
    ++ apply functional_extensionality.
       intros [y z].
       reflexivity.
  + intros a b c H3 H4 u v x σ.
    cbn.
    unfold state_map.
    change (fun o => ((u <<< v) (fst o), snd o))
        with ((fun o => (v (fst o), snd o)) >>> (fun o : b * s => (u (fst o), snd o))).
    apply functor_map_identity.
Qed.

Definition state_apply `{Monad m} {s a b}
    (f : state_t s m (a -> b)) (fs : state_t s m a)
  : state_t s m b :=
  fun x =>
    let* u := f x in
    let* v := fs (snd u) in
    pure (fst u (fst v), snd v).

Definition state_pure `{Monad m} {s a} (x : a) : state_t s m a :=
  fun s => pure (x, s).

Instance state_Applicative `(Monad m) : Applicative (state_t s m) :=
  { pure := @state_pure m _ _ _ s
  ; apply := @state_apply m _ _ _ s
  }.

#[refine]
Instance state_Applicative' `(Monad' m) : Applicative' (state_t s m) := {}.

Proof.
  + intros a Ha Ha' v σ.
    cbn.
    unfold state_pure, state_apply.
    rewrite bind_left_identity.
    cbn.
    replace (fun v0 : a * s => pure (id (fst v0), snd v0))
      with (fun v0 : a * s => pure v0).
    ++ apply bind_right_identity.
    ++ apply functional_extensionality.
       now intros [r σ'].
  + intros a b c Hc Hc' u v w σ.
    cbn.
    unfold state_apply, state_pure.
    cbn.
    repeat rewrite bind_associativity.
    repeat rewrite bind_left_identity.
    repeat rewrite bind_associativity.
    cbn.
    match goal with
    | |- bind _ ?f === bind _ ?g => assert (R : f === g); [| now rewrite R ]
    end.
    intros [f σ'].
    cbn.
    repeat rewrite bind_associativity.
    repeat rewrite bind_left_identity.
    repeat rewrite bind_associativity.
    match goal with
    | |- bind _ ?f === bind _ ?g => assert (R : f === g); [| now rewrite R ]
    end.
    intros [g σ''].
    cbn.
    repeat rewrite bind_associativity.
    repeat rewrite bind_left_identity.
    repeat rewrite bind_associativity.
    cbn.
    match goal with
    | |- bind _ ?f === bind _ ?g => assert (R : f === g); [| now rewrite R ]
    end.
    intros [h σ'''].
    cbn.
    now repeat rewrite bind_left_identity.
  + intros a b Hb Hb' v x.
    cbn.
    intros σ.
    unfold state_apply, state_pure.
    now repeat rewrite bind_left_identity.
  + intros a b Hb Hb'.
    intros u y σ.
    cbn.
    unfold state_apply, state_pure.
    rewrite bind_left_identity; cbn.
    apply bind_morphism.
    intros [f σ'].
    now rewrite bind_left_identity.
  + intros a b Hb Hb' g x σ.
    cbn.
    unfold state_map, state_apply, state_pure.
    rewrite bind_left_identity.
    cbn.
    apply bind_map.
Qed.

Definition state_bind `{Monad m} {s a b}
  (r : state_t s m a) (f : a -> state_t s m b)
  : state_t s m b :=
  fun x =>
    let* u := r x in
    f (fst u) (snd u).

Instance state_Monad `(Monad m) : Monad (state_t s m) :=
  { bind := @state_bind m _ _ _ s
  }.

#[refine]
Instance state_Monad' `(Monad' m) : Monad' (state_t s m) := {}.

Proof.
  + intros a b Hb Hb' x f σ.
    cbn.
    unfold state_bind, state_pure.
    now rewrite bind_left_identity.
  + intros a Ha Ha' x σ.
    cbn.
    unfold state_bind, state_pure.
    replace (fun u : a * s => pure (fst u, snd u))
      with (fun u : a * s => pure u).
    ++ now rewrite bind_right_identity.
    ++ apply functional_extensionality.
       now intros [y σ'].
  + intros a b c Hc Hc' f g h σ.
    cbn.
    unfold state_bind, state_pure.
    rewrite bind_associativity.
    now apply bind_morphism.
  + intros a b Hb Hb' x f g equ σ.
    apply bind_morphism.
    intros [y σ'].
    apply equ.
  + intros a b Hb Hb' x f σ.
    cbn.
    unfold state_map, state_bind, state_pure.
    apply bind_map.
Qed.

Definition state (s : Type) : Type -> Type := state_t s id.

Definition run_state {s a} (r : state s a) (x : s) : (a * s) :=
  r x.

Definition eval_state {s a} (r : state s a) (x : s) : a :=
  fst <$> (r x).

Definition exec_state {s a} (r : state s a) (x : s) : s :=
  snd <$> (r x).

Instance state_MonadState `(Applicative m) : MonadState s (state_t s m) :=
  { get := fun s => pure (s, s)
  ; put := fun s _ => pure (tt, s)
  }.
