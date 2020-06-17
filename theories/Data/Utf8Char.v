From Base Require Export Init Equality Byte Bytestring Int Option.

#[local] Open Scope i63_scope.
#[local] Open Scope byte_scope.

(** We introduce <<uchar>>, for “unicode character” (more precisely, UTF-8
    characters). *)

(** * Definition *)

Inductive uchar : Type :=
| uchar_var_1 : byte -> uchar
| uchar_var_2 : byte -> byte -> uchar
| uchar_var_3 : byte -> byte -> byte -> uchar
| uchar_var_4 : byte -> byte -> byte -> byte -> uchar.

Declare Scope uchar_scope.
Delimit Scope uchar_scope with uchar.
Bind Scope uchar_scope with uchar.

(** * Equality *)

Definition uchar_equalb (c c' : uchar) : bool :=
  match c, c' with
  | uchar_var_1 x, uchar_var_1 x' => x == x'
  | uchar_var_2 x y, uchar_var_2 x' y' => (x == x') && (y == y')
  | uchar_var_3 x y z, uchar_var_3 x' y' z' => (x == x') && (y == y') && (z == z')
  | uchar_var_4 x y z r, uchar_var_4 x' y' z' r' =>
    (x == x') && (y == y') && (z == z') && (r == r')
  | _, _ => false
  end.

Instance uchar_Equ : Equ uchar :=
  { equalb := uchar_equalb }.

#[refine]
Instance uchar_EquL : EquL uchar := {}.

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

(** * Function *)

#[local]
Definition unpack2 (l : bytestring) : option (byte * byte * bytestring) :=
  let* r1 := unpack l in
  let* r2 := unpack (snd r1) in
  pure (fst r1, fst r2, snd r2).

#[local]
Definition unpack3 (l : bytestring) : option (byte * byte * byte * bytestring) :=
  let* r1 := unpack l in
  let* r2 := unpack (snd r1) in
  let* r3 := unpack (snd r2) in
  pure (fst r1, fst r2, fst r3, snd r3).

Definition unpack_ut8 (l : bytestring) : option (uchar * bytestring) :=
  match unpack l with
  | Some (x, rst) => if i63_of_byte x <=? 127 (* variant 1 *)
                then Some (uchar_var_1 x, rst)
                else if i63_of_byte x <=? 223 (* variant 2 *)
                then match unpack rst with
                     | Some (y, rst) =>
                       if i63_of_byte y <=? 191
                       then Some (uchar_var_2 x y, rst)
                       else None
                     | None => None
                     end
                else if i63_of_byte x <=? 239 (* variant 3 *)
                then match unpack2 rst with
                     | Some (y, z, rst) =>
                       if (i63_of_byte y <=? 191) && (i63_of_byte z <=? 191)
                       then Some (uchar_var_3 x y z, rst)
                       else None
                     | _ => None
                     end
                else if i63_of_byte x <=? 247 (* variant 4 *)
                then match unpack3 rst with
                     | Some (y,  z,  r,  rst) =>
                       if (i63_of_byte y <=? 191) &&
                              (i63_of_byte z <=? 191) &&
                              (i63_of_byte r <=? 191)
                       then Some (uchar_var_4 x y z r, rst)
                       else None
                     | _ => None
                     end
                     else None
  | _ => None
  end.

(** * Notation *)

(** Currently, the supported escape characters are:

      - <<\0>> (the <<NULL>> character)
      - <<\n>> (the newline character)
      - <<\t>> (the TAB character)
      - <<\r>> (the carriage return character) *)

#[local]
Definition list_byte_of_uchar (c : uchar) : list byte :=
  match c with
  | uchar_var_1 x => [x]
  | uchar_var_2 x y => [x; y]
  | uchar_var_3 x y z  => [x; y; z]
  | uchar_var_4 x y z r => [x; y; z; r]
  end.

#[local]
Definition uchar_of_list_byte_fmt (x : list byte) : option uchar :=
  let* x := unpack_ut8 <$> Bytestring.bytestring_of_list_byte_fmt x in
  match x with
  | Some (x, ""%bytestring) => Some x
  | _ => None
  end.

String Notation uchar uchar_of_list_byte_fmt list_byte_of_uchar : uchar_scope.
