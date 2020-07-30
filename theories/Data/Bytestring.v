From Coq Require Import Program.Equality FunInd.
From Base Require Export Init Byte Equality Option Int.

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
Instance bytes_EquL : EquL bytestring := {}.

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
  | "\"%byte :: "x"%byte :: "0"%byte :: "0"%byte :: rst => bytes_cons "\x00" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "0"%byte :: "1"%byte :: rst => bytes_cons "\x01" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "0"%byte :: "2"%byte :: rst => bytes_cons "\x02" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "0"%byte :: "3"%byte :: rst => bytes_cons "\x03" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "0"%byte :: "4"%byte :: rst => bytes_cons "\x04" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "0"%byte :: "5"%byte :: rst => bytes_cons "\x05" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "0"%byte :: "6"%byte :: rst => bytes_cons "\x06" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "0"%byte :: "7"%byte :: rst => bytes_cons "\x07" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "0"%byte :: "8"%byte :: rst => bytes_cons "\x08" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "0"%byte :: "9"%byte :: rst => bytes_cons "\x09" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "0"%byte :: "a"%byte :: rst => bytes_cons "\x0a" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "0"%byte :: "b"%byte :: rst => bytes_cons "\x0b" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "0"%byte :: "c"%byte :: rst => bytes_cons "\x0c" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "0"%byte :: "d"%byte :: rst => bytes_cons "\x0d" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "0"%byte :: "e"%byte :: rst => bytes_cons "\x0e" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "0"%byte :: "f"%byte :: rst => bytes_cons "\x0f" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "1"%byte :: "0"%byte :: rst => bytes_cons "\x10" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "1"%byte :: "1"%byte :: rst => bytes_cons "\x11" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "1"%byte :: "2"%byte :: rst => bytes_cons "\x12" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "1"%byte :: "3"%byte :: rst => bytes_cons "\x13" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "1"%byte :: "4"%byte :: rst => bytes_cons "\x14" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "1"%byte :: "5"%byte :: rst => bytes_cons "\x15" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "1"%byte :: "6"%byte :: rst => bytes_cons "\x16" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "1"%byte :: "7"%byte :: rst => bytes_cons "\x17" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "1"%byte :: "8"%byte :: rst => bytes_cons "\x18" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "1"%byte :: "9"%byte :: rst => bytes_cons "\x19" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "1"%byte :: "a"%byte :: rst => bytes_cons "\x1a" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "1"%byte :: "b"%byte :: rst => bytes_cons "\x1b" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "1"%byte :: "c"%byte :: rst => bytes_cons "\x1c" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "1"%byte :: "d"%byte :: rst => bytes_cons "\x1d" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "1"%byte :: "e"%byte :: rst => bytes_cons "\x1e" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "1"%byte :: "f"%byte :: rst => bytes_cons "\x1f" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "2"%byte :: "0"%byte :: rst => bytes_cons "\x20" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "2"%byte :: "1"%byte :: rst => bytes_cons "\x21" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "2"%byte :: "2"%byte :: rst => bytes_cons "\x22" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "2"%byte :: "3"%byte :: rst => bytes_cons "\x23" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "2"%byte :: "4"%byte :: rst => bytes_cons "\x24" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "2"%byte :: "5"%byte :: rst => bytes_cons "\x25" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "2"%byte :: "6"%byte :: rst => bytes_cons "\x26" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "2"%byte :: "7"%byte :: rst => bytes_cons "\x27" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "2"%byte :: "8"%byte :: rst => bytes_cons "\x28" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "2"%byte :: "9"%byte :: rst => bytes_cons "\x29" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "2"%byte :: "a"%byte :: rst => bytes_cons "\x2a" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "2"%byte :: "b"%byte :: rst => bytes_cons "\x2b" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "2"%byte :: "c"%byte :: rst => bytes_cons "\x2c" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "2"%byte :: "d"%byte :: rst => bytes_cons "\x2d" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "2"%byte :: "e"%byte :: rst => bytes_cons "\x2e" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "2"%byte :: "f"%byte :: rst => bytes_cons "\x2f" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "3"%byte :: "0"%byte :: rst => bytes_cons "\x30" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "3"%byte :: "1"%byte :: rst => bytes_cons "\x31" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "3"%byte :: "2"%byte :: rst => bytes_cons "\x32" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "3"%byte :: "3"%byte :: rst => bytes_cons "\x33" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "3"%byte :: "4"%byte :: rst => bytes_cons "\x34" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "3"%byte :: "5"%byte :: rst => bytes_cons "\x35" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "3"%byte :: "6"%byte :: rst => bytes_cons "\x36" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "3"%byte :: "7"%byte :: rst => bytes_cons "\x37" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "3"%byte :: "8"%byte :: rst => bytes_cons "\x38" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "3"%byte :: "9"%byte :: rst => bytes_cons "\x39" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "3"%byte :: "a"%byte :: rst => bytes_cons "\x3a" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "3"%byte :: "b"%byte :: rst => bytes_cons "\x3b" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "3"%byte :: "c"%byte :: rst => bytes_cons "\x3c" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "3"%byte :: "d"%byte :: rst => bytes_cons "\x3d" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "3"%byte :: "e"%byte :: rst => bytes_cons "\x3e" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "3"%byte :: "f"%byte :: rst => bytes_cons "\x3f" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "4"%byte :: "0"%byte :: rst => bytes_cons "\x40" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "4"%byte :: "1"%byte :: rst => bytes_cons "\x41" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "4"%byte :: "2"%byte :: rst => bytes_cons "\x42" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "4"%byte :: "3"%byte :: rst => bytes_cons "\x43" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "4"%byte :: "4"%byte :: rst => bytes_cons "\x44" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "4"%byte :: "5"%byte :: rst => bytes_cons "\x45" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "4"%byte :: "6"%byte :: rst => bytes_cons "\x46" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "4"%byte :: "7"%byte :: rst => bytes_cons "\x47" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "4"%byte :: "8"%byte :: rst => bytes_cons "\x48" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "4"%byte :: "9"%byte :: rst => bytes_cons "\x49" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "4"%byte :: "a"%byte :: rst => bytes_cons "\x4a" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "4"%byte :: "b"%byte :: rst => bytes_cons "\x4b" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "4"%byte :: "c"%byte :: rst => bytes_cons "\x4c" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "4"%byte :: "d"%byte :: rst => bytes_cons "\x4d" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "4"%byte :: "e"%byte :: rst => bytes_cons "\x4e" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "4"%byte :: "f"%byte :: rst => bytes_cons "\x4f" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "5"%byte :: "0"%byte :: rst => bytes_cons "\x50" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "5"%byte :: "1"%byte :: rst => bytes_cons "\x51" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "5"%byte :: "2"%byte :: rst => bytes_cons "\x52" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "5"%byte :: "3"%byte :: rst => bytes_cons "\x53" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "5"%byte :: "4"%byte :: rst => bytes_cons "\x54" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "5"%byte :: "5"%byte :: rst => bytes_cons "\x55" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "5"%byte :: "6"%byte :: rst => bytes_cons "\x56" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "5"%byte :: "7"%byte :: rst => bytes_cons "\x57" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "5"%byte :: "8"%byte :: rst => bytes_cons "\x58" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "5"%byte :: "9"%byte :: rst => bytes_cons "\x59" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "5"%byte :: "a"%byte :: rst => bytes_cons "\x5a" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "5"%byte :: "b"%byte :: rst => bytes_cons "\x5b" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "5"%byte :: "c"%byte :: rst => bytes_cons "\x5c" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "5"%byte :: "d"%byte :: rst => bytes_cons "\x5d" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "5"%byte :: "e"%byte :: rst => bytes_cons "\x5e" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "5"%byte :: "f"%byte :: rst => bytes_cons "\x5f" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "6"%byte :: "0"%byte :: rst => bytes_cons "\x60" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "6"%byte :: "1"%byte :: rst => bytes_cons "\x61" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "6"%byte :: "2"%byte :: rst => bytes_cons "\x62" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "6"%byte :: "3"%byte :: rst => bytes_cons "\x63" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "6"%byte :: "4"%byte :: rst => bytes_cons "\x64" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "6"%byte :: "5"%byte :: rst => bytes_cons "\x65" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "6"%byte :: "6"%byte :: rst => bytes_cons "\x66" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "6"%byte :: "7"%byte :: rst => bytes_cons "\x67" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "6"%byte :: "8"%byte :: rst => bytes_cons "\x68" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "6"%byte :: "9"%byte :: rst => bytes_cons "\x69" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "6"%byte :: "a"%byte :: rst => bytes_cons "\x6a" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "6"%byte :: "b"%byte :: rst => bytes_cons "\x6b" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "6"%byte :: "c"%byte :: rst => bytes_cons "\x6c" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "6"%byte :: "d"%byte :: rst => bytes_cons "\x6d" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "6"%byte :: "e"%byte :: rst => bytes_cons "\x6e" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "6"%byte :: "f"%byte :: rst => bytes_cons "\x6f" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "7"%byte :: "0"%byte :: rst => bytes_cons "\x70" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "7"%byte :: "1"%byte :: rst => bytes_cons "\x71" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "7"%byte :: "2"%byte :: rst => bytes_cons "\x72" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "7"%byte :: "3"%byte :: rst => bytes_cons "\x73" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "7"%byte :: "4"%byte :: rst => bytes_cons "\x74" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "7"%byte :: "5"%byte :: rst => bytes_cons "\x75" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "7"%byte :: "6"%byte :: rst => bytes_cons "\x76" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "7"%byte :: "7"%byte :: rst => bytes_cons "\x77" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "7"%byte :: "8"%byte :: rst => bytes_cons "\x78" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "7"%byte :: "9"%byte :: rst => bytes_cons "\x79" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "7"%byte :: "a"%byte :: rst => bytes_cons "\x7a" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "7"%byte :: "b"%byte :: rst => bytes_cons "\x7b" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "7"%byte :: "c"%byte :: rst => bytes_cons "\x7c" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "7"%byte :: "d"%byte :: rst => bytes_cons "\x7d" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "7"%byte :: "e"%byte :: rst => bytes_cons "\x7e" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "7"%byte :: "f"%byte :: rst => bytes_cons "\x7f" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "8"%byte :: "0"%byte :: rst => bytes_cons "\x80" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "8"%byte :: "1"%byte :: rst => bytes_cons "\x81" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "8"%byte :: "2"%byte :: rst => bytes_cons "\x82" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "8"%byte :: "3"%byte :: rst => bytes_cons "\x83" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "8"%byte :: "4"%byte :: rst => bytes_cons "\x84" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "8"%byte :: "5"%byte :: rst => bytes_cons "\x85" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "8"%byte :: "6"%byte :: rst => bytes_cons "\x86" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "8"%byte :: "7"%byte :: rst => bytes_cons "\x87" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "8"%byte :: "8"%byte :: rst => bytes_cons "\x88" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "8"%byte :: "9"%byte :: rst => bytes_cons "\x89" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "8"%byte :: "a"%byte :: rst => bytes_cons "\x8a" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "8"%byte :: "b"%byte :: rst => bytes_cons "\x8b" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "8"%byte :: "c"%byte :: rst => bytes_cons "\x8c" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "8"%byte :: "d"%byte :: rst => bytes_cons "\x8d" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "8"%byte :: "e"%byte :: rst => bytes_cons "\x8e" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "8"%byte :: "f"%byte :: rst => bytes_cons "\x8f" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "9"%byte :: "0"%byte :: rst => bytes_cons "\x90" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "9"%byte :: "1"%byte :: rst => bytes_cons "\x91" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "9"%byte :: "2"%byte :: rst => bytes_cons "\x92" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "9"%byte :: "3"%byte :: rst => bytes_cons "\x93" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "9"%byte :: "4"%byte :: rst => bytes_cons "\x94" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "9"%byte :: "5"%byte :: rst => bytes_cons "\x95" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "9"%byte :: "6"%byte :: rst => bytes_cons "\x96" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "9"%byte :: "7"%byte :: rst => bytes_cons "\x97" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "9"%byte :: "8"%byte :: rst => bytes_cons "\x98" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "9"%byte :: "9"%byte :: rst => bytes_cons "\x99" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "9"%byte :: "a"%byte :: rst => bytes_cons "\x9a" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "9"%byte :: "b"%byte :: rst => bytes_cons "\x9b" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "9"%byte :: "c"%byte :: rst => bytes_cons "\x9c" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "9"%byte :: "d"%byte :: rst => bytes_cons "\x9d" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "9"%byte :: "e"%byte :: rst => bytes_cons "\x9e" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "9"%byte :: "f"%byte :: rst => bytes_cons "\x9f" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "a"%byte :: "0"%byte :: rst => bytes_cons "\xa0" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "a"%byte :: "1"%byte :: rst => bytes_cons "\xa1" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "a"%byte :: "2"%byte :: rst => bytes_cons "\xa2" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "a"%byte :: "3"%byte :: rst => bytes_cons "\xa3" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "a"%byte :: "4"%byte :: rst => bytes_cons "\xa4" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "a"%byte :: "5"%byte :: rst => bytes_cons "\xa5" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "a"%byte :: "6"%byte :: rst => bytes_cons "\xa6" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "a"%byte :: "7"%byte :: rst => bytes_cons "\xa7" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "a"%byte :: "8"%byte :: rst => bytes_cons "\xa8" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "a"%byte :: "9"%byte :: rst => bytes_cons "\xa9" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "a"%byte :: "a"%byte :: rst => bytes_cons "\xaa" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "a"%byte :: "b"%byte :: rst => bytes_cons "\xab" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "a"%byte :: "c"%byte :: rst => bytes_cons "\xac" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "a"%byte :: "d"%byte :: rst => bytes_cons "\xad" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "a"%byte :: "e"%byte :: rst => bytes_cons "\xae" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "a"%byte :: "f"%byte :: rst => bytes_cons "\xaf" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "b"%byte :: "0"%byte :: rst => bytes_cons "\xb0" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "b"%byte :: "1"%byte :: rst => bytes_cons "\xb1" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "b"%byte :: "2"%byte :: rst => bytes_cons "\xb2" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "b"%byte :: "3"%byte :: rst => bytes_cons "\xb3" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "b"%byte :: "4"%byte :: rst => bytes_cons "\xb4" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "b"%byte :: "5"%byte :: rst => bytes_cons "\xb5" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "b"%byte :: "6"%byte :: rst => bytes_cons "\xb6" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "b"%byte :: "7"%byte :: rst => bytes_cons "\xb7" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "b"%byte :: "8"%byte :: rst => bytes_cons "\xb8" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "b"%byte :: "9"%byte :: rst => bytes_cons "\xb9" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "b"%byte :: "a"%byte :: rst => bytes_cons "\xba" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "b"%byte :: "b"%byte :: rst => bytes_cons "\xbb" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "b"%byte :: "c"%byte :: rst => bytes_cons "\xbc" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "b"%byte :: "d"%byte :: rst => bytes_cons "\xbd" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "b"%byte :: "e"%byte :: rst => bytes_cons "\xbe" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "b"%byte :: "f"%byte :: rst => bytes_cons "\xbf" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "c"%byte :: "0"%byte :: rst => bytes_cons "\xc0" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "c"%byte :: "1"%byte :: rst => bytes_cons "\xc1" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "c"%byte :: "2"%byte :: rst => bytes_cons "\xc2" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "c"%byte :: "3"%byte :: rst => bytes_cons "\xc3" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "c"%byte :: "4"%byte :: rst => bytes_cons "\xc4" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "c"%byte :: "5"%byte :: rst => bytes_cons "\xc5" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "c"%byte :: "6"%byte :: rst => bytes_cons "\xc6" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "c"%byte :: "7"%byte :: rst => bytes_cons "\xc7" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "c"%byte :: "8"%byte :: rst => bytes_cons "\xc8" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "c"%byte :: "9"%byte :: rst => bytes_cons "\xc9" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "c"%byte :: "a"%byte :: rst => bytes_cons "\xca" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "c"%byte :: "b"%byte :: rst => bytes_cons "\xcb" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "c"%byte :: "c"%byte :: rst => bytes_cons "\xcc" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "c"%byte :: "d"%byte :: rst => bytes_cons "\xcd" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "c"%byte :: "e"%byte :: rst => bytes_cons "\xce" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "c"%byte :: "f"%byte :: rst => bytes_cons "\xcf" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "d"%byte :: "0"%byte :: rst => bytes_cons "\xd0" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "d"%byte :: "1"%byte :: rst => bytes_cons "\xd1" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "d"%byte :: "2"%byte :: rst => bytes_cons "\xd2" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "d"%byte :: "3"%byte :: rst => bytes_cons "\xd3" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "d"%byte :: "4"%byte :: rst => bytes_cons "\xd4" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "d"%byte :: "5"%byte :: rst => bytes_cons "\xd5" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "d"%byte :: "6"%byte :: rst => bytes_cons "\xd6" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "d"%byte :: "7"%byte :: rst => bytes_cons "\xd7" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "d"%byte :: "8"%byte :: rst => bytes_cons "\xd8" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "d"%byte :: "9"%byte :: rst => bytes_cons "\xd9" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "d"%byte :: "a"%byte :: rst => bytes_cons "\xda" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "d"%byte :: "b"%byte :: rst => bytes_cons "\xdb" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "d"%byte :: "c"%byte :: rst => bytes_cons "\xdc" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "d"%byte :: "d"%byte :: rst => bytes_cons "\xdd" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "d"%byte :: "e"%byte :: rst => bytes_cons "\xde" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "d"%byte :: "f"%byte :: rst => bytes_cons "\xdf" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "e"%byte :: "0"%byte :: rst => bytes_cons "\xe0" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "e"%byte :: "1"%byte :: rst => bytes_cons "\xe1" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "e"%byte :: "2"%byte :: rst => bytes_cons "\xe2" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "e"%byte :: "3"%byte :: rst => bytes_cons "\xe3" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "e"%byte :: "4"%byte :: rst => bytes_cons "\xe4" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "e"%byte :: "5"%byte :: rst => bytes_cons "\xe5" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "e"%byte :: "6"%byte :: rst => bytes_cons "\xe6" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "e"%byte :: "7"%byte :: rst => bytes_cons "\xe7" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "e"%byte :: "8"%byte :: rst => bytes_cons "\xe8" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "e"%byte :: "9"%byte :: rst => bytes_cons "\xe9" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "e"%byte :: "a"%byte :: rst => bytes_cons "\xea" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "e"%byte :: "b"%byte :: rst => bytes_cons "\xeb" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "e"%byte :: "c"%byte :: rst => bytes_cons "\xec" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "e"%byte :: "d"%byte :: rst => bytes_cons "\xed" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "e"%byte :: "e"%byte :: rst => bytes_cons "\xee" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "e"%byte :: "f"%byte :: rst => bytes_cons "\xef" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "f"%byte :: "0"%byte :: rst => bytes_cons "\xf0" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "f"%byte :: "1"%byte :: rst => bytes_cons "\xf1" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "f"%byte :: "2"%byte :: rst => bytes_cons "\xf2" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "f"%byte :: "3"%byte :: rst => bytes_cons "\xf3" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "f"%byte :: "4"%byte :: rst => bytes_cons "\xf4" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "f"%byte :: "5"%byte :: rst => bytes_cons "\xf5" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "f"%byte :: "6"%byte :: rst => bytes_cons "\xf6" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "f"%byte :: "7"%byte :: rst => bytes_cons "\xf7" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "f"%byte :: "8"%byte :: rst => bytes_cons "\xf8" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "f"%byte :: "9"%byte :: rst => bytes_cons "\xf9" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "f"%byte :: "a"%byte :: rst => bytes_cons "\xfa" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "f"%byte :: "b"%byte :: rst => bytes_cons "\xfb" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "f"%byte :: "c"%byte :: rst => bytes_cons "\xfc" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "f"%byte :: "d"%byte :: rst => bytes_cons "\xfd" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "f"%byte :: "e"%byte :: rst => bytes_cons "\xfe" <$> bytestring_of_list_byte_fmt rst
  | "\"%byte :: "x"%byte :: "f"%byte :: "f"%byte :: rst => bytes_cons "\xff" <$> bytestring_of_list_byte_fmt rst
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

Fixpoint bytestring_fold_left {α}
    (b : bytestring) (f : α -> byte -> α) (init : α)
  : α :=
  match b with
  | bytes_cons x rst => bytestring_fold_left rst f (f init x)
  | bytes_nil => init
  end.

Definition length (b : bytestring) : i63 :=
  bytestring_fold_left b (fun x _ => x + 1) 0.

Definition nat_length (b : bytestring) : nat :=
  bytestring_fold_left b (fun x _ => x + 1)%nat 0%nat.

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

Fixpoint bytestring_of_list (l : list byte) : bytestring :=
  match l with
  | x :: rst => bytes_cons x (bytestring_of_list rst)
  | [] => bytes_nil
  end.

Module BytestringExtraction.
  Extract Inductive bytestring =>
  "Coqbase.Bytestring.t" [
      "Coqbase.Bytestring.pack"
      "Coqbase.Bytestring.empty"
    ] "Coqbase.Bytestring.case".

  Extract Inlined Constant bytes_equalb => "Coqbase.Bytestring.equal".
  Extract Inlined Constant append => "Coqbase.Bytestring.append".
  Extract Inlined Constant length => "Coqbase.Bytestring.length".
  Extract Inlined Constant bytestring_of_int => "Coqbase.Bytestring.bytestring_of_int".
  Extract Inlined Constant int_of_bytestring => "Coqbase.Bytestring.int_of_bytestring".
  Extract Inlined Constant split => "Coqbase.Bytestring.split".
  Extract Inlined Constant bytestring_of_list => "Coqbase.Bytestring.of_list".
End BytestringExtraction.
