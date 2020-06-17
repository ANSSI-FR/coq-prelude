(* coq-base -- A base library to program in Coq
 * Copyright (C) 2018–2020 ANSSI
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see <http://www.gnu.org/licenses/>.
 *)

From Coq Require Export Init.Byte Strings.Byte.
From Base Require Import Init Equality Int.

(** The Coq standard library provides the [ascii] type, whose terms consist in a
    collection of height booleans, and whose notation does not provide any
    particular escape characters we tend to take for granted (e.g., <<\n>>,
    <<\t>>, etc.).

    On the contrary, <<coq-base>> relies on the <<byte>> type to model
    characters. *)

(** * Notation *)

(** We introduce the necessary conversion functions to provide a nice string
    notation for <<byte>>, which include in particular the following escape
    characters:

      - <<\0>> (the <<NULL>> character)
      - <<\n>> (the newline character)
      - <<\t>> (the TAB character)
      - <<\r>> (the carriage return character)
      - <<\xHH>>, where <<HH>> is an hexadecimal code *)

#[local]
Definition byte_of_bytes_fmt (x : list byte) : option byte :=
  match x with
  | [x5c; x30] => Some x00 (* \0 *)
  | [x5c; x6e] => Some x0a (* \n *)
  | [x5c; x72] => Some x0d (* \r *)
  | [x5c; x74] => Some x09 (* \t *)
  | [x5c; x78; x30; x30]=> Some x00 (* \x00 *)
  | [x5c; x78; x30; x31]=> Some x01 (* \x01 *)
  | [x5c; x78; x30; x32]=> Some x02 (* \x02 *)
  | [x5c; x78; x30; x33]=> Some x03 (* \x03 *)
  | [x5c; x78; x30; x34]=> Some x04 (* \x04 *)
  | [x5c; x78; x30; x35]=> Some x05 (* \x05 *)
  | [x5c; x78; x30; x36]=> Some x06 (* \x06 *)
  | [x5c; x78; x30; x37]=> Some x07 (* \x07 *)
  | [x5c; x78; x30; x38]=> Some x08 (* \x08 *)
  | [x5c; x78; x30; x39]=> Some x09 (* \x09 *)
  | [x5c; x78; x30; x61]=> Some x0a (* \x0a *)
  | [x5c; x78; x30; x62]=> Some x0b (* \x0b *)
  | [x5c; x78; x30; x63]=> Some x0c (* \x0c *)
  | [x5c; x78; x30; x64]=> Some x0d (* \x0d *)
  | [x5c; x78; x30; x65]=> Some x0e (* \x0e *)
  | [x5c; x78; x30; x66]=> Some x0f (* \x0f *)
  | [x5c; x78; x31; x30]=> Some x10 (* \x10 *)
  | [x5c; x78; x31; x31]=> Some x11 (* \x11 *)
  | [x5c; x78; x31; x32]=> Some x12 (* \x12 *)
  | [x5c; x78; x31; x33]=> Some x13 (* \x13 *)
  | [x5c; x78; x31; x34]=> Some x14 (* \x14 *)
  | [x5c; x78; x31; x35]=> Some x15 (* \x15 *)
  | [x5c; x78; x31; x36]=> Some x16 (* \x16 *)
  | [x5c; x78; x31; x37]=> Some x17 (* \x17 *)
  | [x5c; x78; x31; x38]=> Some x18 (* \x18 *)
  | [x5c; x78; x31; x39]=> Some x19 (* \x19 *)
  | [x5c; x78; x31; x61]=> Some x1a (* \x1a *)
  | [x5c; x78; x31; x62]=> Some x1b (* \x1b *)
  | [x5c; x78; x31; x63]=> Some x1c (* \x1c *)
  | [x5c; x78; x31; x64]=> Some x1d (* \x1d *)
  | [x5c; x78; x31; x65]=> Some x1e (* \x1e *)
  | [x5c; x78; x31; x66]=> Some x1f (* \x1f *)
  | [x5c; x78; x32; x30]=> Some x20 (* \x20 *)
  | [x5c; x78; x32; x31]=> Some x21 (* \x21 *)
  | [x5c; x78; x32; x32]=> Some x22 (* \x22 *)
  | [x5c; x78; x32; x33]=> Some x23 (* \x23 *)
  | [x5c; x78; x32; x34]=> Some x24 (* \x24 *)
  | [x5c; x78; x32; x35]=> Some x25 (* \x25 *)
  | [x5c; x78; x32; x36]=> Some x26 (* \x26 *)
  | [x5c; x78; x32; x37]=> Some x27 (* \x27 *)
  | [x5c; x78; x32; x38]=> Some x28 (* \x28 *)
  | [x5c; x78; x32; x39]=> Some x29 (* \x29 *)
  | [x5c; x78; x32; x61]=> Some x2a (* \x2a *)
  | [x5c; x78; x32; x62]=> Some x2b (* \x2b *)
  | [x5c; x78; x32; x63]=> Some x2c (* \x2c *)
  | [x5c; x78; x32; x64]=> Some x2d (* \x2d *)
  | [x5c; x78; x32; x65]=> Some x2e (* \x2e *)
  | [x5c; x78; x32; x66]=> Some x2f (* \x2f *)
  | [x5c; x78; x33; x30]=> Some x30 (* \x30 *)
  | [x5c; x78; x33; x31]=> Some x31 (* \x31 *)
  | [x5c; x78; x33; x32]=> Some x32 (* \x32 *)
  | [x5c; x78; x33; x33]=> Some x33 (* \x33 *)
  | [x5c; x78; x33; x34]=> Some x34 (* \x34 *)
  | [x5c; x78; x33; x35]=> Some x35 (* \x35 *)
  | [x5c; x78; x33; x36]=> Some x36 (* \x36 *)
  | [x5c; x78; x33; x37]=> Some x37 (* \x37 *)
  | [x5c; x78; x33; x38]=> Some x38 (* \x38 *)
  | [x5c; x78; x33; x39]=> Some x39 (* \x39 *)
  | [x5c; x78; x33; x61]=> Some x3a (* \x3a *)
  | [x5c; x78; x33; x62]=> Some x3b (* \x3b *)
  | [x5c; x78; x33; x63]=> Some x3c (* \x3c *)
  | [x5c; x78; x33; x64]=> Some x3d (* \x3d *)
  | [x5c; x78; x33; x65]=> Some x3e (* \x3e *)
  | [x5c; x78; x33; x66]=> Some x3f (* \x3f *)
  | [x5c; x78; x34; x30]=> Some x40 (* \x40 *)
  | [x5c; x78; x34; x31]=> Some x41 (* \x41 *)
  | [x5c; x78; x34; x32]=> Some x42 (* \x42 *)
  | [x5c; x78; x34; x33]=> Some x43 (* \x43 *)
  | [x5c; x78; x34; x34]=> Some x44 (* \x44 *)
  | [x5c; x78; x34; x35]=> Some x45 (* \x45 *)
  | [x5c; x78; x34; x36]=> Some x46 (* \x46 *)
  | [x5c; x78; x34; x37]=> Some x47 (* \x47 *)
  | [x5c; x78; x34; x38]=> Some x48 (* \x48 *)
  | [x5c; x78; x34; x39]=> Some x49 (* \x49 *)
  | [x5c; x78; x34; x61]=> Some x4a (* \x4a *)
  | [x5c; x78; x34; x62]=> Some x4b (* \x4b *)
  | [x5c; x78; x34; x63]=> Some x4c (* \x4c *)
  | [x5c; x78; x34; x64]=> Some x4d (* \x4d *)
  | [x5c; x78; x34; x65]=> Some x4e (* \x4e *)
  | [x5c; x78; x34; x66]=> Some x4f (* \x4f *)
  | [x5c; x78; x35; x30]=> Some x50 (* \x50 *)
  | [x5c; x78; x35; x31]=> Some x51 (* \x51 *)
  | [x5c; x78; x35; x32]=> Some x52 (* \x52 *)
  | [x5c; x78; x35; x33]=> Some x53 (* \x53 *)
  | [x5c; x78; x35; x34]=> Some x54 (* \x54 *)
  | [x5c; x78; x35; x35]=> Some x55 (* \x55 *)
  | [x5c; x78; x35; x36]=> Some x56 (* \x56 *)
  | [x5c; x78; x35; x37]=> Some x57 (* \x57 *)
  | [x5c; x78; x35; x38]=> Some x58 (* \x58 *)
  | [x5c; x78; x35; x39]=> Some x59 (* \x59 *)
  | [x5c; x78; x35; x61]=> Some x5a (* \x5a *)
  | [x5c; x78; x35; x62]=> Some x5b (* \x5b *)
  | [x5c; x78; x35; x63]=> Some x5c (* \x5c *)
  | [x5c; x78; x35; x64]=> Some x5d (* \x5d *)
  | [x5c; x78; x35; x65]=> Some x5e (* \x5e *)
  | [x5c; x78; x35; x66]=> Some x5f (* \x5f *)
  | [x5c; x78; x36; x30]=> Some x60 (* \x60 *)
  | [x5c; x78; x36; x31]=> Some x61 (* \x61 *)
  | [x5c; x78; x36; x32]=> Some x62 (* \x62 *)
  | [x5c; x78; x36; x33]=> Some x63 (* \x63 *)
  | [x5c; x78; x36; x34]=> Some x64 (* \x64 *)
  | [x5c; x78; x36; x35]=> Some x65 (* \x65 *)
  | [x5c; x78; x36; x36]=> Some x66 (* \x66 *)
  | [x5c; x78; x36; x37]=> Some x67 (* \x67 *)
  | [x5c; x78; x36; x38]=> Some x68 (* \x68 *)
  | [x5c; x78; x36; x39]=> Some x69 (* \x69 *)
  | [x5c; x78; x36; x61]=> Some x6a (* \x6a *)
  | [x5c; x78; x36; x62]=> Some x6b (* \x6b *)
  | [x5c; x78; x36; x63]=> Some x6c (* \x6c *)
  | [x5c; x78; x36; x64]=> Some x6d (* \x6d *)
  | [x5c; x78; x36; x65]=> Some x6e (* \x6e *)
  | [x5c; x78; x36; x66]=> Some x6f (* \x6f *)
  | [x5c; x78; x37; x30]=> Some x70 (* \x70 *)
  | [x5c; x78; x37; x31]=> Some x71 (* \x71 *)
  | [x5c; x78; x37; x32]=> Some x72 (* \x72 *)
  | [x5c; x78; x37; x33]=> Some x73 (* \x73 *)
  | [x5c; x78; x37; x34]=> Some x74 (* \x74 *)
  | [x5c; x78; x37; x35]=> Some x75 (* \x75 *)
  | [x5c; x78; x37; x36]=> Some x76 (* \x76 *)
  | [x5c; x78; x37; x37]=> Some x77 (* \x77 *)
  | [x5c; x78; x37; x38]=> Some x78 (* \x78 *)
  | [x5c; x78; x37; x39]=> Some x79 (* \x79 *)
  | [x5c; x78; x37; x61]=> Some x7a (* \x7a *)
  | [x5c; x78; x37; x62]=> Some x7b (* \x7b *)
  | [x5c; x78; x37; x63]=> Some x7c (* \x7c *)
  | [x5c; x78; x37; x64]=> Some x7d (* \x7d *)
  | [x5c; x78; x37; x65]=> Some x7e (* \x7e *)
  | [x5c; x78; x37; x66]=> Some x7f (* \x7f *)
  | [x5c; x78; x38; x30]=> Some x80 (* \x80 *)
  | [x5c; x78; x38; x31]=> Some x81 (* \x81 *)
  | [x5c; x78; x38; x32]=> Some x82 (* \x82 *)
  | [x5c; x78; x38; x33]=> Some x83 (* \x83 *)
  | [x5c; x78; x38; x34]=> Some x84 (* \x84 *)
  | [x5c; x78; x38; x35]=> Some x85 (* \x85 *)
  | [x5c; x78; x38; x36]=> Some x86 (* \x86 *)
  | [x5c; x78; x38; x37]=> Some x87 (* \x87 *)
  | [x5c; x78; x38; x38]=> Some x88 (* \x88 *)
  | [x5c; x78; x38; x39]=> Some x89 (* \x89 *)
  | [x5c; x78; x38; x61]=> Some x8a (* \x8a *)
  | [x5c; x78; x38; x62]=> Some x8b (* \x8b *)
  | [x5c; x78; x38; x63]=> Some x8c (* \x8c *)
  | [x5c; x78; x38; x64]=> Some x8d (* \x8d *)
  | [x5c; x78; x38; x65]=> Some x8e (* \x8e *)
  | [x5c; x78; x38; x66]=> Some x8f (* \x8f *)
  | [x5c; x78; x39; x30]=> Some x90 (* \x90 *)
  | [x5c; x78; x39; x31]=> Some x91 (* \x91 *)
  | [x5c; x78; x39; x32]=> Some x92 (* \x92 *)
  | [x5c; x78; x39; x33]=> Some x93 (* \x93 *)
  | [x5c; x78; x39; x34]=> Some x94 (* \x94 *)
  | [x5c; x78; x39; x35]=> Some x95 (* \x95 *)
  | [x5c; x78; x39; x36]=> Some x96 (* \x96 *)
  | [x5c; x78; x39; x37]=> Some x97 (* \x97 *)
  | [x5c; x78; x39; x38]=> Some x98 (* \x98 *)
  | [x5c; x78; x39; x39]=> Some x99 (* \x99 *)
  | [x5c; x78; x39; x61]=> Some x9a (* \x9a *)
  | [x5c; x78; x39; x62]=> Some x9b (* \x9b *)
  | [x5c; x78; x39; x63]=> Some x9c (* \x9c *)
  | [x5c; x78; x39; x64]=> Some x9d (* \x9d *)
  | [x5c; x78; x39; x65]=> Some x9e (* \x9e *)
  | [x5c; x78; x39; x66]=> Some x9f (* \x9f *)
  | [x5c; x78; x61; x30]=> Some xa0 (* \xa0 *)
  | [x5c; x78; x61; x31]=> Some xa1 (* \xa1 *)
  | [x5c; x78; x61; x32]=> Some xa2 (* \xa2 *)
  | [x5c; x78; x61; x33]=> Some xa3 (* \xa3 *)
  | [x5c; x78; x61; x34]=> Some xa4 (* \xa4 *)
  | [x5c; x78; x61; x35]=> Some xa5 (* \xa5 *)
  | [x5c; x78; x61; x36]=> Some xa6 (* \xa6 *)
  | [x5c; x78; x61; x37]=> Some xa7 (* \xa7 *)
  | [x5c; x78; x61; x38]=> Some xa8 (* \xa8 *)
  | [x5c; x78; x61; x39]=> Some xa9 (* \xa9 *)
  | [x5c; x78; x61; x61]=> Some xaa (* \xaa *)
  | [x5c; x78; x61; x62]=> Some xab (* \xab *)
  | [x5c; x78; x61; x63]=> Some xac (* \xac *)
  | [x5c; x78; x61; x64]=> Some xad (* \xad *)
  | [x5c; x78; x61; x65]=> Some xae (* \xae *)
  | [x5c; x78; x61; x66]=> Some xaf (* \xaf *)
  | [x5c; x78; x62; x30]=> Some xb0 (* \xb0 *)
  | [x5c; x78; x62; x31]=> Some xb1 (* \xb1 *)
  | [x5c; x78; x62; x32]=> Some xb2 (* \xb2 *)
  | [x5c; x78; x62; x33]=> Some xb3 (* \xb3 *)
  | [x5c; x78; x62; x34]=> Some xb4 (* \xb4 *)
  | [x5c; x78; x62; x35]=> Some xb5 (* \xb5 *)
  | [x5c; x78; x62; x36]=> Some xb6 (* \xb6 *)
  | [x5c; x78; x62; x37]=> Some xb7 (* \xb7 *)
  | [x5c; x78; x62; x38]=> Some xb8 (* \xb8 *)
  | [x5c; x78; x62; x39]=> Some xb9 (* \xb9 *)
  | [x5c; x78; x62; x61]=> Some xba (* \xba *)
  | [x5c; x78; x62; x62]=> Some xbb (* \xbb *)
  | [x5c; x78; x62; x63]=> Some xbc (* \xbc *)
  | [x5c; x78; x62; x64]=> Some xbd (* \xbd *)
  | [x5c; x78; x62; x65]=> Some xbe (* \xbe *)
  | [x5c; x78; x62; x66]=> Some xbf (* \xbf *)
  | [x5c; x78; x63; x30]=> Some xc0 (* \xc0 *)
  | [x5c; x78; x63; x31]=> Some xc1 (* \xc1 *)
  | [x5c; x78; x63; x32]=> Some xc2 (* \xc2 *)
  | [x5c; x78; x63; x33]=> Some xc3 (* \xc3 *)
  | [x5c; x78; x63; x34]=> Some xc4 (* \xc4 *)
  | [x5c; x78; x63; x35]=> Some xc5 (* \xc5 *)
  | [x5c; x78; x63; x36]=> Some xc6 (* \xc6 *)
  | [x5c; x78; x63; x37]=> Some xc7 (* \xc7 *)
  | [x5c; x78; x63; x38]=> Some xc8 (* \xc8 *)
  | [x5c; x78; x63; x39]=> Some xc9 (* \xc9 *)
  | [x5c; x78; x63; x61]=> Some xca (* \xca *)
  | [x5c; x78; x63; x62]=> Some xcb (* \xcb *)
  | [x5c; x78; x63; x63]=> Some xcc (* \xcc *)
  | [x5c; x78; x63; x64]=> Some xcd (* \xcd *)
  | [x5c; x78; x63; x65]=> Some xce (* \xce *)
  | [x5c; x78; x63; x66]=> Some xcf (* \xcf *)
  | [x5c; x78; x64; x30]=> Some xd0 (* \xd0 *)
  | [x5c; x78; x64; x31]=> Some xd1 (* \xd1 *)
  | [x5c; x78; x64; x32]=> Some xd2 (* \xd2 *)
  | [x5c; x78; x64; x33]=> Some xd3 (* \xd3 *)
  | [x5c; x78; x64; x34]=> Some xd4 (* \xd4 *)
  | [x5c; x78; x64; x35]=> Some xd5 (* \xd5 *)
  | [x5c; x78; x64; x36]=> Some xd6 (* \xd6 *)
  | [x5c; x78; x64; x37]=> Some xd7 (* \xd7 *)
  | [x5c; x78; x64; x38]=> Some xd8 (* \xd8 *)
  | [x5c; x78; x64; x39]=> Some xd9 (* \xd9 *)
  | [x5c; x78; x64; x61]=> Some xda (* \xda *)
  | [x5c; x78; x64; x62]=> Some xdb (* \xdb *)
  | [x5c; x78; x64; x63]=> Some xdc (* \xdc *)
  | [x5c; x78; x64; x64]=> Some xdd (* \xdd *)
  | [x5c; x78; x64; x65]=> Some xde (* \xde *)
  | [x5c; x78; x64; x66]=> Some xdf (* \xdf *)
  | [x5c; x78; x65; x30]=> Some xe0 (* \xe0 *)
  | [x5c; x78; x65; x31]=> Some xe1 (* \xe1 *)
  | [x5c; x78; x65; x32]=> Some xe2 (* \xe2 *)
  | [x5c; x78; x65; x33]=> Some xe3 (* \xe3 *)
  | [x5c; x78; x65; x34]=> Some xe4 (* \xe4 *)
  | [x5c; x78; x65; x35]=> Some xe5 (* \xe5 *)
  | [x5c; x78; x65; x36]=> Some xe6 (* \xe6 *)
  | [x5c; x78; x65; x37]=> Some xe7 (* \xe7 *)
  | [x5c; x78; x65; x38]=> Some xe8 (* \xe8 *)
  | [x5c; x78; x65; x39]=> Some xe9 (* \xe9 *)
  | [x5c; x78; x65; x61]=> Some xea (* \xea *)
  | [x5c; x78; x65; x62]=> Some xeb (* \xeb *)
  | [x5c; x78; x65; x63]=> Some xec (* \xec *)
  | [x5c; x78; x65; x64]=> Some xed (* \xed *)
  | [x5c; x78; x65; x65]=> Some xee (* \xee *)
  | [x5c; x78; x65; x66]=> Some xef (* \xef *)
  | [x5c; x78; x66; x30]=> Some xf0 (* \xf0 *)
  | [x5c; x78; x66; x31]=> Some xf1 (* \xf1 *)
  | [x5c; x78; x66; x32]=> Some xf2 (* \xf2 *)
  | [x5c; x78; x66; x33]=> Some xf3 (* \xf3 *)
  | [x5c; x78; x66; x34]=> Some xf4 (* \xf4 *)
  | [x5c; x78; x66; x35]=> Some xf5 (* \xf5 *)
  | [x5c; x78; x66; x36]=> Some xf6 (* \xf6 *)
  | [x5c; x78; x66; x37]=> Some xf7 (* \xf7 *)
  | [x5c; x78; x66; x38]=> Some xf8 (* \xf8 *)
  | [x5c; x78; x66; x39]=> Some xf9 (* \xf9 *)
  | [x5c; x78; x66; x61]=> Some xfa (* \xfa *)
  | [x5c; x78; x66; x62]=> Some xfb (* \xfb *)
  | [x5c; x78; x66; x63]=> Some xfc (* \xfc *)
  | [x5c; x78; x66; x64]=> Some xfd (* \xfd *)
  | [x5c; x78; x66; x65]=> Some xfe (* \xfe *)
  | [x5c; x78; x66; x66]=> Some xff (* \xff *)
  | [x] => Some x
  | _ => None
  end.

#[local]
Definition bytes_of_byte (x : byte) : list byte := [x].

String Notation byte byte_of_bytes_fmt bytes_of_byte : byte_scope.

(** * Equality *)

Instance byte_Equ : Equ byte :=
  { equalb := Byte.eqb }.

Axiom byte_equal_equalb_equiv : forall x y : byte, x = y <-> (x =? y)%byte = true.

#[program]
Instance byte_EquL : EquL byte.

Next Obligation.
  apply byte_equal_equalb_equiv.
Qed.

(** * Functions *)

Definition i63_of_byte (c : byte) : i63 :=
  match c with
  | x00 => 0
  | x01 => 1
  | x02 => 2
  | x03 => 3
  | x04 => 4
  | x05 => 5
  | x06 => 6
  | x07 => 7
  | x08 => 8
  | x09 => 9
  | x0a => 10
  | x0b => 11
  | x0c => 12
  | x0d => 13
  | x0e => 14
  | x0f => 15
  | x10 => 16
  | x11 => 17
  | x12 => 18
  | x13 => 19
  | x14 => 20
  | x15 => 21
  | x16 => 22
  | x17 => 23
  | x18 => 24
  | x19 => 25
  | x1a => 26
  | x1b => 27
  | x1c => 28
  | x1d => 29
  | x1e => 30
  | x1f => 31
  | x20 => 32
  | x21 => 33
  | x22 => 34
  | x23 => 35
  | x24 => 36
  | x25 => 37
  | x26 => 38
  | x27 => 39
  | x28 => 40
  | x29 => 41
  | x2a => 42
  | x2b => 43
  | x2c => 44
  | x2d => 45
  | x2e => 46
  | x2f => 47
  | x30 => 48
  | x31 => 49
  | x32 => 50
  | x33 => 51
  | x34 => 52
  | x35 => 53
  | x36 => 54
  | x37 => 55
  | x38 => 56
  | x39 => 57
  | x3a => 58
  | x3b => 59
  | x3c => 60
  | x3d => 61
  | x3e => 62
  | x3f => 63
  | x40 => 64
  | x41 => 65
  | x42 => 66
  | x43 => 67
  | x44 => 68
  | x45 => 69
  | x46 => 70
  | x47 => 71
  | x48 => 72
  | x49 => 73
  | x4a => 74
  | x4b => 75
  | x4c => 76
  | x4d => 77
  | x4e => 78
  | x4f => 79
  | x50 => 80
  | x51 => 81
  | x52 => 82
  | x53 => 83
  | x54 => 84
  | x55 => 85
  | x56 => 86
  | x57 => 87
  | x58 => 88
  | x59 => 89
  | x5a => 90
  | x5b => 91
  | x5c => 92
  | x5d => 93
  | x5e => 94
  | x5f => 95
  | x60 => 96
  | x61 => 97
  | x62 => 98
  | x63 => 99
  | x64 => 100
  | x65 => 101
  | x66 => 102
  | x67 => 103
  | x68 => 104
  | x69 => 105
  | x6a => 106
  | x6b => 107
  | x6c => 108
  | x6d => 109
  | x6e => 110
  | x6f => 111
  | x70 => 112
  | x71 => 113
  | x72 => 114
  | x73 => 115
  | x74 => 116
  | x75 => 117
  | x76 => 118
  | x77 => 119
  | x78 => 120
  | x79 => 121
  | x7a => 122
  | x7b => 123
  | x7c => 124
  | x7d => 125
  | x7e => 126
  | x7f => 127
  | x80 => 128
  | x81 => 129
  | x82 => 130
  | x83 => 131
  | x84 => 132
  | x85 => 133
  | x86 => 134
  | x87 => 135
  | x88 => 136
  | x89 => 137
  | x8a => 138
  | x8b => 139
  | x8c => 140
  | x8d => 141
  | x8e => 142
  | x8f => 143
  | x90 => 144
  | x91 => 145
  | x92 => 146
  | x93 => 147
  | x94 => 148
  | x95 => 149
  | x96 => 150
  | x97 => 151
  | x98 => 152
  | x99 => 153
  | x9a => 154
  | x9b => 155
  | x9c => 156
  | x9d => 157
  | x9e => 158
  | x9f => 159
  | xa0 => 160
  | xa1 => 161
  | xa2 => 162
  | xa3 => 163
  | xa4 => 164
  | xa5 => 165
  | xa6 => 166
  | xa7 => 167
  | xa8 => 168
  | xa9 => 169
  | xaa => 170
  | xab => 171
  | xac => 172
  | xad => 173
  | xae => 174
  | xaf => 175
  | xb0 => 176
  | xb1 => 177
  | xb2 => 178
  | xb3 => 179
  | xb4 => 180
  | xb5 => 181
  | xb6 => 182
  | xb7 => 183
  | xb8 => 184
  | xb9 => 185
  | xba => 186
  | xbb => 187
  | xbc => 188
  | xbd => 189
  | xbe => 190
  | xbf => 191
  | xc0 => 192
  | xc1 => 193
  | xc2 => 194
  | xc3 => 195
  | xc4 => 196
  | xc5 => 197
  | xc6 => 198
  | xc7 => 199
  | xc8 => 200
  | xc9 => 201
  | xca => 202
  | xcb => 203
  | xcc => 204
  | xcd => 205
  | xce => 206
  | xcf => 207
  | xd0 => 208
  | xd1 => 209
  | xd2 => 210
  | xd3 => 211
  | xd4 => 212
  | xd5 => 213
  | xd6 => 214
  | xd7 => 215
  | xd8 => 216
  | xd9 => 217
  | xda => 218
  | xdb => 219
  | xdc => 220
  | xdd => 221
  | xde => 222
  | xdf => 223
  | xe0 => 224
  | xe1 => 225
  | xe2 => 226
  | xe3 => 227
  | xe4 => 228
  | xe5 => 229
  | xe6 => 230
  | xe7 => 231
  | xe8 => 232
  | xe9 => 233
  | xea => 234
  | xeb => 235
  | xec => 236
  | xed => 237
  | xee => 238
  | xef => 239
  | xf0 => 240
  | xf1 => 241
  | xf2 => 242
  | xf3 => 243
  | xf4 => 244
  | xf5 => 245
  | xf6 => 246
  | xf7 => 247
  | xf8 => 248
  | xf9 => 249
  | xfa => 250
  | xfb => 251
  | xfc => 252
  | xfd => 253
  | xfe => 254
  | xff => 255
  end.

#[local] Open Scope i63_scope.
#[local] Open Scope byte_scope.

Definition digit_of_byte (x : byte) : option i63 :=
  match x with
  | "0" => Some 0
  | "1" => Some 1
  | "2" => Some 2
  | "3" => Some 3
  | "4" => Some 4
  | "5" => Some 5
  | "6" => Some 6
  | "7" => Some 7
  | "8" => Some 8
  | "9" => Some 9
  | _ => None
  end.

Definition uppercase_ascii (x : byte) : byte :=
  match x with
  | "a" => "A"
  | "b" => "B"
  | "c" => "C"
  | "d" => "D"
  | "e" => "E"
  | "f" => "F"
  | "g" => "G"
  | "h" => "H"
  | "i" => "I"
  | "j" => "J"
  | "k" => "K"
  | "l" => "L"
  | "m" => "M"
  | "n" => "N"
  | "o" => "O"
  | "p" => "P"
  | "q" => "Q"
  | "r" => "R"
  | "s" => "S"
  | "t" => "T"
  | "u" => "U"
  | "v" => "V"
  | "w" => "W"
  | "x" => "X"
  | "y" => "Y"
  | "z" => "Z"
  | x => x
  end.

Definition lowercase_ascii (x : byte) : byte :=
  match x with
  | "A" => "a"
  | "B" => "b"
  | "C" => "c"
  | "D" => "d"
  | "E" => "e"
  | "F" => "f"
  | "G" => "g"
  | "H" => "h"
  | "I" => "i"
  | "J" => "j"
  | "K" => "k"
  | "L" => "l"
  | "M" => "m"
  | "N" => "n"
  | "O" => "o"
  | "P" => "p"
  | "Q" => "q"
  | "R" => "r"
  | "S" => "s"
  | "T" => "t"
  | "U" => "u"
  | "V" => "v"
  | "W" => "w"
  | "X" => "x"
  | "Y" => "y"
  | "Z" => "z"
  | x => x
  end.

Definition byte_ltb (c1 c2 : byte) : bool :=
  i63_of_byte c1 <? i63_of_byte c2.

Infix "<?" := byte_ltb : byte_scope.
Notation "'#b' c" := (c%byte) (at level 200, only parsing).

(** * Extraction *)

Module ByteExtraction.
  Extract Inductive byte => char
  ["'\x00'" "'\x01'" "'\x02'" "'\x03'" "'\x04'" "'\x05'" "'\x06'" "'\x07'" "'\x08'" "'\t'" "'\n'" "'\x0b'" "'\x0c'" "'\r'" "'\x0e'" "'\x0f'" "'\x10'" "'\x11'" "'\x12'" "'\x13'" "'\x14'" "'\x15'" "'\x16'" "'\x17'" "'\x18'" "'\x19'" "'\x1a'" "'\x1b'" "'\x1c'" "'\x1d'" "'\x1e'" "'\x1f'" "' '" "'!'" "'""'" "'#'" "'$'" "'%'" "'&'" "'\''" "'('" "')'" "'*'" "'+'" "','" "'-'" "'.'" "'/'" "'0'" "'1'" "'2'" "'3'" "'4'" "'5'" "'6'" "'7'" "'8'" "'9'" "':'" "';'" "'<'" "'='" "'>'" "'?'" "'@'" "'A'" "'B'" "'C'" "'D'" "'E'" "'F'" "'G'" "'H'" "'I'" "'J'" "'K'" "'L'" "'M'" "'N'" "'O'" "'P'" "'Q'" "'R'" "'S'" "'T'" "'U'" "'V'" "'W'" "'X'" "'Y'" "'Z'" "'['" "'\\'" "']'" "'^'" "'_'" "'`'" "'a'" "'b'" "'c'" "'d'" "'e'" "'f'" "'g'" "'h'" "'i'" "'j'" "'k'" "'l'" "'m'" "'n'" "'o'" "'p'" "'q'" "'r'" "'s'" "'t'" "'u'" "'v'" "'w'" "'x'" "'y'" "'z'" "'{'" "'|'" "'}'" "'~'" "'\x7f'" "'\x80'" "'\x81'" "'\x82'" "'\x83'" "'\x84'" "'\x85'" "'\x86'" "'\x87'" "'\x88'" "'\x89'" "'\x8a'" "'\x8b'" "'\x8c'" "'\x8d'" "'\x8e'" "'\x8f'" "'\x90'" "'\x91'" "'\x92'" "'\x93'" "'\x94'" "'\x95'" "'\x96'" "'\x97'" "'\x98'" "'\x99'" "'\x9a'" "'\x9b'" "'\x9c'" "'\x9d'" "'\x9e'" "'\x9f'" "'\xa0'" "'\xa1'" "'\xa2'" "'\xa3'" "'\xa4'" "'\xa5'" "'\xa6'" "'\xa7'" "'\xa8'" "'\xa9'" "'\xaa'" "'\xab'" "'\xac'" "'\xad'" "'\xae'" "'\xaf'" "'\xb0'" "'\xb1'" "'\xb2'" "'\xb3'" "'\xb4'" "'\xb5'" "'\xb6'" "'\xb7'" "'\xb8'" "'\xb9'" "'\xba'" "'\xbb'" "'\xbc'" "'\xbd'" "'\xbe'" "'\xbf'" "'\xc0'" "'\xc1'" "'\xc2'" "'\xc3'" "'\xc4'" "'\xc5'" "'\xc6'" "'\xc7'" "'\xc8'" "'\xc9'" "'\xca'" "'\xcb'" "'\xcc'" "'\xcd'" "'\xce'" "'\xcf'" "'\xd0'" "'\xd1'" "'\xd2'" "'\xd3'" "'\xd4'" "'\xd5'" "'\xd6'" "'\xd7'" "'\xd8'" "'\xd9'" "'\xda'" "'\xdb'" "'\xdc'" "'\xdd'" "'\xde'" "'\xdf'" "'\xe0'" "'\xe1'" "'\xe2'" "'\xe3'" "'\xe4'" "'\xe5'" "'\xe6'" "'\xe7'" "'\xe8'" "'\xe9'" "'\xea'" "'\xeb'" "'\xec'" "'\xed'" "'\xee'" "'\xef'" "'\xf0'" "'\xf1'" "'\xf2'" "'\xf3'" "'\xf4'" "'\xf5'" "'\xf6'" "'\xf7'" "'\xf8'" "'\xf9'" "'\xfa'" "'\xfb'" "'\xfc'" "'\xfd'" "'\xfe'" "'\xff'"].

  Extract Inlined Constant Byte.eqb => "(=)".
End ByteExtraction.
