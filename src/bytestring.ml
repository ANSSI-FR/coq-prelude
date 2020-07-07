open Option

type t = { offset : int ; size : int ; data : string ; sub : bool }

let of_string b = { offset = 0; size = String.length b; data = b ; sub = false }

let to_string b = if b.sub then String.sub b.data b.offset b.size else b.data

let shift b =
  if 0 < b.size
  then Some { offset = b.offset + 1 ; size = b.size - 1 ; data = b.data ; sub = true }
  else None

let unsafe_get_char b x =
  String.get (b.data) (b.offset + x)

let get_char b x =
  try Some (String.get (b.data) (b.offset + x))
  with _ -> None

let equal b1 b2 =
  let rec aux i =
    i < 0 || (unsafe_get_char b1 i == unsafe_get_char b2 i && aux (i - 1)) in
  b1.size == b2.size && aux (b1.size - 1)

let unpack b =
  bind (get_char b 0) (fun c -> bind (shift b) (fun rst -> Some (c, rst)))

let pack (c, b) =
  let init = fun i -> if i == 0 then c else unsafe_get_char b (i - 1) in
  let buffer = String.init (b.size + 1) init in
  { offset = 0 ; data = buffer ; size = b.size + 1 ; sub = false }

let case f1 f0 b =
  match unpack b with
  | Some (x, rst) -> f1 x rst
  | _ -> f0 ()

let empty =
  { offset = 0 ; data = "" ; size = 0 ; sub = false }

let append b1 b2 =
  let init = fun i ->
    if i < b1.size
    then String.get b1.data (b1.offset + i)
    else String.get b2.data (b2.offset + (i - b1.size)) in
  let buffer = String.init (b1.size + b2.size) init in
  { offset = 0; size = b1.size + b2.size; data = buffer ; sub = false }

let length b = b.size

let bytestring_of_int x = of_string (string_of_int x)

let int_of_bytestring b = int_of_string_opt b.data

let split b x =
  if x <= b.size
  then Some ({ offset = b.offset; size = x; data = b.data ; sub = true },
             { offset = b.offset + x; size = b.size - x; data = b.data ; sub = true })
  else None

let of_list l = List.to_seq l |> String.of_seq |> of_string

let read_line x = Stdlib.read_line x |> of_string

let print_bytestring b = to_string b |> print_string

let write fd b ofs len =
  Unix.write_substring fd b.data (b.offset + ofs) len

let read fd len =
  let buff = Bytes.create len in
  let size = Unix.read fd buff 0 0 in
  { data = Bytes.to_string buff ; offset = 0 ; size = size ; sub = (len = size) }
