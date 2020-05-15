From Coq Require Import Program.Equality FunInd.
From Base Require Export Init Byte Equality Option Ring Int.

#[local] Open Scope i63_scope.

Inductive bytestring :=
| bytes_cons : byte -> bytestring -> bytestring
| bytes_nil : bytestring.

Declare Scope bytestring_scope.
Delimit Scope bytestring_scope with bytestring.
Bind Scope bytestring_scope with bytestring.

Register bytestring as base.data.bytestring.type.
Register bytes_cons as base.data.bytestring.bytes_cons.
Register bytes_nil as base.data.bytestring.bytes_nil.

Definition unpack (x : bytestring) : option (byte * bytestring) :=
  match x with
  | bytes_cons x rst => Some (x, rst)
  | _ => None
  end.

#[local]
Fixpoint rev_aux (x : bytestring) (acc : bytestring) : bytestring :=
  match x with
  | bytes_nil => acc
  | bytes_cons x rst => rev_aux rst (bytes_cons x acc)
  end.

#[local]
Definition rev (x : bytestring) : bytestring :=
  rev_aux x bytes_nil.

#[local]
Fixpoint split_aux (input : bytestring) (x : i63) (acc : bytestring) : option (bytestring * bytestring) :=
  if x == 0
  then Some (rev acc, input)
  else match input with
       | bytes_cons c rst => split_aux rst (x - 1) (bytes_cons c acc)
       | bytes_nil => None
       end.

Definition split (input : bytestring) (x : i63) : option (bytestring * bytestring) :=
  split_aux input x bytes_nil.

Definition pack (x : byte * bytestring) : bytestring :=
  bytes_cons (fst x) (snd x).

Fixpoint append (x y : bytestring) : bytestring :=
  match x with
  | bytes_cons x rst => bytes_cons x (append rst y)
  | bytes_nil => y
  end.

Infix "++" := append : bytestring_scope.

Inductive bytes_equal : bytestring -> bytestring -> Prop :=
| bytes_cons_equal (c : byte) (rst rst' : bytestring) (equ : bytes_equal rst rst')
  : bytes_equal (bytes_cons c rst) (bytes_cons c rst')
| bytes_nil_equal : bytes_equal bytes_nil bytes_nil.

Lemma bytes_equal_eq_equiv (x y : bytestring) :
  x = y <-> bytes_equal x y.

Proof.
  split; intros equ.
  + subst.
    induction y; constructor.
    apply IHy.
  + induction equ.
    ++ rewrite IHequ.
       reflexivity.
    ++ reflexivity.
Qed.

Fixpoint bytes_equalb (x y : bytestring) : bool :=
  match x, y with
  | bytes_cons x rst, bytes_cons y rst' => (x == y) && bytes_equalb rst rst'
  | bytes_nil, bytes_nil => true
  | _, _ => false
  end.

Instance bytes_Equ : Equ bytestring :=
  { equalb := bytes_equalb }.

Lemma bytes_equal_equal_equiv (x y : bytestring) :
  x = y <-> x === y.

Proof.
  reflexivity.
Qed.

Functional Scheme bytes_equalb_ind := Induction for bytes_equalb Sort Type.

#[refine]
Instance bytes_Equ' : Equ' bytestring := {}.

Proof.
  intros x y.
  functional induction (bytes_equalb x y).
  + split.
    ++ intros equ.
       cbn.
       apply Bool.andb_true_iff.
       inversion equ; subst.
       split.
       +++ destruct y0; reflexivity.
       +++ cbn in IHb.
           now apply IHb.
    ++ intros equ.
       cbn in equ.
       apply Bool.andb_true_iff in equ.
       destruct equ as [ equ1 equ2 ].
       cbn in IHb.
       apply IHb in equ2.
       apply byte_dec_bl in equ1.
       now subst.
  + split; discriminate.
  + split; discriminate.
  + split; reflexivity.
Qed.

#[local]
Fixpoint bytestring_of_list_byte_fmt (i : list byte) : option (bytestring) :=
  match i with
  | "\"%byte :: "0"%byte :: rst => bytes_cons "\0" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "n"%byte :: rst => bytes_cons "\n" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "r"%byte :: rst => bytes_cons "\r" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "t"%byte :: rst => bytes_cons "\t" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "\"%byte :: rst => bytes_cons "\" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: _     :: rst => None
  | x     :: rst          => bytes_cons x <$> bytestring_of_list_byte_fmt rst
  | [] => Some bytes_nil
  end.

Fixpoint list_byte_of_bytestring (x : bytestring) : list byte :=
  match x with
  | bytes_cons x rst => x :: list_byte_of_bytestring rst
  | bytes_nil => []
  end.

String Notation bytestring bytestring_of_list_byte_fmt list_byte_of_bytestring
  : bytestring_scope.

#[local]
Fixpoint length_aux `{Semiring i} (b : bytestring) : i :=
  match b with
  | bytes_cons _ rst => one + length_aux rst
  | _ => zero
  end.

Definition length (b : bytestring) : i63 := length_aux b.

Definition nat_length (b : bytestring) : nat := length_aux b.

#[local] Open Scope i63_scope.

#[local]
Fixpoint int_of_bytestring_aux (x : bytestring) (acc : i63) : option i63 :=
  match x with
  | bytes_cons x rst => let* x := digit_of_byte x in
                        int_of_bytestring_aux rst (10 * acc + x)
  | bytes_nil => pure acc
  end.

Definition int_of_bytestring (x : bytestring) : option i63 :=
  match x with
  | bytes_cons "-"%byte rst => (fun x => -1 * x) <$> int_of_bytestring_aux rst 0
  | _ => int_of_bytestring_aux x 0
  end.

#[local]
Definition byte_of_digit (x : i63) : byte :=
  if x <? 1 then "0"
  else if x <? 2 then "1"
  else if x <? 3 then "2"
  else if x <? 4 then "3"
  else if x <? 5 then "4"
  else if x <? 6 then "5"
  else if x <? 7 then "6"
  else if x <? 8 then "7"
  else if x <? 9 then "8"
  else "9".

Unset Guard Checking.
Fixpoint bytestring_of_int_aux (x : i63) (acc : bytestring)
    {struct x}
  : bytestring :=
  let d := x / 10 in
  let r := x mod 10 in
  let acc' := (bytes_cons (byte_of_digit r) acc) in
  if 0 <? d
  then bytestring_of_int_aux d acc'
  else acc'.
Set Guard Checking.

(* One way to implement this without unsetting guard checking is to
   use the <<Program>> framework, with the <<measure>> feature. One
   working implementation is:

<<
#[program, local]
Fixpoint bytestring_of_int_aux (x : i63) (acc : bytestring)
    {measure (abs_nat x)}
  : bytestring :=
  let d := x / 10 in
  let r := x mod 10 in
  let acc' := (bytes_cons (byte_of_digit r) acc) in
  (if 0 <? d as b return 0 <? d = b -> bytestring
   then fun equ => bytestring_of_int_aux d acc'
   else fun equ => acc') eq_refl.

Axiom (bytestring_of_int_axiom : forall n,
          (0 < PeanoNat.Nat.div n 10)%nat -> (0 < n)%nat).

Next Obligation.
  rewrite lt_ltb_equiv in equ.
  apply abs_nat_lt_inj in equ.
  rewrite abs_nat_div_inj in equ.
  rewrite abs_nat_div_inj.
  revert equ.
  generalize (abs_nat x).
  change (abs_nat 10) with 10%nat.
  intros n equ.
  apply PeanoNat.Nat.div_lt.
  + now apply bytestring_of_int_axiom.
  + repeat constructor.
Defined.
>>

   But it does not compute very well. *)

Definition bytestring_of_int (x : i63) : bytestring :=
  if 0 <? x
  then bytestring_of_int_aux x ""
  else bytes_cons "-" (bytestring_of_int_aux (-1 * x) "").

Module BytestringExtraction.
  Extract Inductive bytestring =>
  "Bytestring.t" [
      "Bytestring.pack"
      "Bytestring.empty"
    ] "Bytestring.case".

  Extract Inlined Constant bytes_equalb => "Bytestring.equal".
  Extract Inlined Constant append => "Bytestring.append".
  Extract Inlined Constant length => "Bytestring.length".
  Extract Inlined Constant bytestring_of_int => "Bytestring.bytestring_of_int".
  Extract Inlined Constant int_of_bytestring => "Bytestring.int_of_bytestring".
  Extract Inlined Constant split => "Bytestring.split".
End BytestringExtraction.
