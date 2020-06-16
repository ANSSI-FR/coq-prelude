From Coq Require Export Init.Byte Strings.Byte Int63.
From Base Require Import Init Equality Int.

(** * Notation *)

#[local]
Definition byte_of_bytes_fmt (x : list byte) : option byte :=
  match x with
  | [x5c; x30] => Some x00 (* \0 *)
  | [x5c; x6e] => Some x0a (* \n *)
  | [x5c; x72] => Some x0d (* \r *)
  | [x5c; x74] => Some x09 (* \t *)
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

Definition int_of_byte (c : byte) : int :=
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

Definition digit_of_byte (x : byte) : option i63 :=
  match x with
  | "0"%byte => Some 0
  | "1"%byte => Some 1
  | "2"%byte => Some 2
  | "3"%byte => Some 3
  | "4"%byte => Some 4
  | "5"%byte => Some 5
  | "6"%byte => Some 6
  | "7"%byte => Some 7
  | "8"%byte => Some 8
  | "9"%byte => Some 9
  | _ => None
  end.

(** * Extraction *)

Module ByteExtraction.
  Extract Inductive byte => char
  ["'\x00'" "'\x01'" "'\x02'" "'\x03'" "'\x04'" "'\x05'" "'\x06'" "'\x07'" "'\x08'" "'\t'" "'\n'" "'\x0b'" "'\x0c'" "'\r'" "'\x0e'" "'\x0f'" "'\x10'" "'\x11'" "'\x12'" "'\x13'" "'\x14'" "'\x15'" "'\x16'" "'\x17'" "'\x18'" "'\x19'" "'\x1a'" "'\x1b'" "'\x1c'" "'\x1d'" "'\x1e'" "'\x1f'" "' '" "'!'" "'""'" "'#'" "'$'" "'%'" "'&'" "'\''" "'('" "')'" "'*'" "'+'" "','" "'-'" "'.'" "'/'" "'0'" "'1'" "'2'" "'3'" "'4'" "'5'" "'6'" "'7'" "'8'" "'9'" "':'" "';'" "'<'" "'='" "'>'" "'?'" "'@'" "'A'" "'B'" "'C'" "'D'" "'E'" "'F'" "'G'" "'H'" "'I'" "'J'" "'K'" "'L'" "'M'" "'N'" "'O'" "'P'" "'Q'" "'R'" "'S'" "'T'" "'U'" "'V'" "'W'" "'X'" "'Y'" "'Z'" "'['" "'\\'" "']'" "'^'" "'_'" "'`'" "'a'" "'b'" "'c'" "'d'" "'e'" "'f'" "'g'" "'h'" "'i'" "'j'" "'k'" "'l'" "'m'" "'n'" "'o'" "'p'" "'q'" "'r'" "'s'" "'t'" "'u'" "'v'" "'w'" "'x'" "'y'" "'z'" "'{'" "'|'" "'}'" "'~'" "'\x7f'" "'\x80'" "'\x81'" "'\x82'" "'\x83'" "'\x84'" "'\x85'" "'\x86'" "'\x87'" "'\x88'" "'\x89'" "'\x8a'" "'\x8b'" "'\x8c'" "'\x8d'" "'\x8e'" "'\x8f'" "'\x90'" "'\x91'" "'\x92'" "'\x93'" "'\x94'" "'\x95'" "'\x96'" "'\x97'" "'\x98'" "'\x99'" "'\x9a'" "'\x9b'" "'\x9c'" "'\x9d'" "'\x9e'" "'\x9f'" "'\xa0'" "'\xa1'" "'\xa2'" "'\xa3'" "'\xa4'" "'\xa5'" "'\xa6'" "'\xa7'" "'\xa8'" "'\xa9'" "'\xaa'" "'\xab'" "'\xac'" "'\xad'" "'\xae'" "'\xaf'" "'\xb0'" "'\xb1'" "'\xb2'" "'\xb3'" "'\xb4'" "'\xb5'" "'\xb6'" "'\xb7'" "'\xb8'" "'\xb9'" "'\xba'" "'\xbb'" "'\xbc'" "'\xbd'" "'\xbe'" "'\xbf'" "'\xc0'" "'\xc1'" "'\xc2'" "'\xc3'" "'\xc4'" "'\xc5'" "'\xc6'" "'\xc7'" "'\xc8'" "'\xc9'" "'\xca'" "'\xcb'" "'\xcc'" "'\xcd'" "'\xce'" "'\xcf'" "'\xd0'" "'\xd1'" "'\xd2'" "'\xd3'" "'\xd4'" "'\xd5'" "'\xd6'" "'\xd7'" "'\xd8'" "'\xd9'" "'\xda'" "'\xdb'" "'\xdc'" "'\xdd'" "'\xde'" "'\xdf'" "'\xe0'" "'\xe1'" "'\xe2'" "'\xe3'" "'\xe4'" "'\xe5'" "'\xe6'" "'\xe7'" "'\xe8'" "'\xe9'" "'\xea'" "'\xeb'" "'\xec'" "'\xed'" "'\xee'" "'\xef'" "'\xf0'" "'\xf1'" "'\xf2'" "'\xf3'" "'\xf4'" "'\xf5'" "'\xf6'" "'\xf7'" "'\xf8'" "'\xf9'" "'\xfa'" "'\xfb'" "'\xfc'" "'\xfd'" "'\xfe'" "'\xff'"].

  Extract Inlined Constant Byte.eqb => "(=)".
End ByteExtraction.
