From Base Require Export Init Equality Bool Byte.
From Coq Require Import Int63.

(** * UTF-8 Wide Characters *)

Inductive wchar : Type :=
| wchar_var_1 : byte -> wchar
| wchar_var_2 : byte -> byte -> wchar
| wchar_var_3 : byte -> byte -> byte -> wchar
| wchar_var_4 : byte -> byte -> byte -> byte -> wchar.

Declare Scope wchar_scope.
Delimit Scope wchar_scope with wchar.
Bind Scope wchar_scope with wchar.

Definition wchar_equalb (c c' : wchar) : bool :=
  match c, c' with
  | wchar_var_1 x, wchar_var_1 x' => x == x'
  | wchar_var_2 x y, wchar_var_2 x' y' => (x == x') && (y == y')
  | wchar_var_3 x y z, wchar_var_3 x' y' z' => (x == x') && (y == y') && (z == z')
  | wchar_var_4 x y z r, wchar_var_4 x' y' z' r' =>
    (x == x') && (y == y') && (z == z') && (r == r')
  | _, _ => false
  end.

Instance wchar_Equ : Equ wchar :=
  { equalb := wchar_equalb }.

#[refine]
Instance wchar_EquL : EquL wchar := {}.

Proof.
  intros x y.
  split; intros equ.
  + inversion equ; subst.
    destruct y;
      repeat (apply andb_true_intro; split);
      now apply Byte.byte_dec_lb.
  + destruct x; destruct y; try discriminate;
      cbn in equ;
      repeat match goal with
             | H : andb _ _ = true |- _ =>
               apply andb_prop in H; destruct H
             | H : Byte.eqb _ _ = true |- _ =>
               apply Byte.byte_dec_bl in H; subst
             end;
      reflexivity.
Qed.

#[local]
Definition list_byte_of_wchar (c : wchar) : list byte :=
  match c with
  | wchar_var_1 x => [x]
  | wchar_var_2 x y => [x; y]
  | wchar_var_3 x y z  => [x; y; z]
  | wchar_var_4 x y z r => [x; y; z; r]
  end.

#[local]
Definition read_wchar (l : list byte) : option (wchar * list byte) :=
  match l with
  | x :: rst => if leb (int_of_byte x) 127 (* variant 1 *)
                then Some (wchar_var_1 x, rst)
                else if leb (int_of_byte x) 223 (* variant 2 *)
                then match rst with
                     | y :: rst =>
                       if leb (int_of_byte y) 191
                       then Some (wchar_var_2 x y, rst)
                       else None
                     | [] => None
                     end
                else if leb (int_of_byte x) 239 (* variant 3 *)
                then match rst with
                     | y :: z :: rst =>
                       if leb (int_of_byte y) 191 && leb (int_of_byte z) 191
                       then Some (wchar_var_3 x y z, rst)
                       else None
                     | _ => None
                     end
                else if leb (int_of_byte x) 247 (* variant 4 *)
                then match rst with
                     | y :: z :: r :: rst =>
                       if leb (int_of_byte y) 191 &&
                              leb (int_of_byte z) 191 &&
                              leb (int_of_byte r) 191
                       then Some (wchar_var_4 x y z r, rst)
                       else None
                     | _ => None
                     end
                     else None
  | _ => None
  end.
