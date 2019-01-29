(** [dup H H'] will duplicate the hypothesis [H], under the name [H'].
    *)
Ltac dup H H' :=
  let T := type of H in
  assert (H': T) by exact H.
