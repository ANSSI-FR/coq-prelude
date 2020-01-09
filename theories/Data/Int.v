From Coq Require Export Int63.
From Coq Require Import Wf Wf_Z Inverse_Image ZArith Recdef.
From Prelude Require Import Init Control Text Byte Bytes Equality Option.

#[local] Close Scope nat_scope.
#[local] Open Scope int63_scope.

Definition lt (x y : int) : Prop := ([|x|]%int63 < [|y|]%int63)%Z.
Definition le (x y : int) : Prop := ([|x|]%int63 <= [|y|]%int63)%Z.

Notation "n < m" := (lt n m) : int63_scope.
Notation "n <= m" := (le n m) : int63_scope.
Notation "n <? m" := (ltb n m) : int63_scope.
Notation "n <=? m" := (leb n m) : int63_scope.

Axiom int_lt_false_spec : forall (x y : int), x <? y = false -> ~ x < y.

Lemma int_div_lt (x y : int) (x_pos : 0 < x) (y_pos : 1 < y) : (x / y) < x.

Proof.
  unfold lt in *.
  rewrite div_spec.
  now apply Z.div_lt.
Qed.

#[program]
Definition wchar_of_digit (x : int) (x_digit : x < 10) : wchar :=
  if x <? 1 then "0"
  else if x <? 2 then "1"
  else if x <? 3 then "2"
  else if x <? 4 then "3"
  else if x <? 5 then "4"
  else if x <? 6 then "5"
  else if x <? 7 then "6"
  else if x <? 8 then "7"
  else if x <? 9 then "8"
  else (if x <? 10 as b return (b = (x <? 10) -> wchar)
  then fun _ => w#"9"
  else _) eq_refl.

Next Obligation.
  symmetry in H.
  now apply int_lt_false_spec in H.
Qed.

#[program]
Fixpoint text_of_int_aux (x : int) (x_digit : 0 < x) (acc : text) {measure (Z.to_nat [|x|])}
  : text :=
  let d := x / 10 in
  let r := x \% 10 in
  let acc' := (TCons (wchar_of_digit r _) acc)%text in
  (if 0 <? d as b return (0 <? d = b -> text)
   then fun _ => text_of_int_aux d _ acc'
   else fun _ => acc') eq_refl.

Next Obligation.
  unfold lt in *.
  rewrite mod_spec.
  now apply Z.mod_pos_bound.
Qed.

Next Obligation.
  now apply ltb_spec in H.
Qed.

Next Obligation.
  apply Z2Nat.inj_lt.
  + apply to_Z_bounded.
  + apply to_Z_bounded.
  + apply int_div_lt.
    ++ exact x_digit.
    ++ constructor.
Qed.

#[program]
Definition text_of_int (x : int) : text :=
  (if 0 <? x as b return (0 <? x = b -> text)
   then fun _ => text_of_int_aux x _ t#""
   else fun _ => t#"0") eq_refl.

Next Obligation.
  now apply ltb_spec in H.
Qed.

Definition bytes_of_int (x : int) : bytes :=
  bytes_of_text (text_of_int x).

Definition digit_of_wchar (x : wchar) : option int :=
  match x with
  | w#"0" => Some 0
  | w#"1" => Some 1
  | w#"2" => Some 2
  | w#"3" => Some 3
  | w#"4" => Some 4
  | w#"5" => Some 5
  | w#"6" => Some 6
  | w#"7" => Some 7
  | w#"8" => Some 8
  | w#"9" => Some 9
  | _ => None
  end.

Fixpoint int_of_text_aux (x : text) (acc : int) : option int :=
  match x with
  | TCons x rst => do let* x := digit_of_wchar x in
                      int_of_text_aux rst (10 * acc + x)
                   end
  | TNil => pure acc
  end.

Definition int_of_text (x : text)  : option int := int_of_text_aux x 0.
Definition int_of_bytes (x : bytes)  : option int := text_of_bytes x >>= int_of_text.
