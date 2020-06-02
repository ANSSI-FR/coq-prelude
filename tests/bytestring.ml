open Coqbase.Bytestring

let%test _ = equal (of_string "foo") (of_string "foo")

let%test _ = not (equal (of_string "foo") (of_string "bar"))

let%test _ = not (equal (of_string "foo") (of_string "foo_"))

let%test _ =
  match unpack (of_string "foo") with
  | Some(c, rst) -> c == 'f' && equal rst (of_string "oo")
  | None -> false

let%test _ = equal (pack ('f', of_string "oo")) (of_string "foo")

let%test _ =
  let input = of_string "foo" in
  match unpack input with
  | Some(r) -> equal input (pack r)
  | None -> false

let%test _ = equal
    (append (of_string "foo ") (of_string "bar"))
    (of_string "foo bar")

let%test _ = length (of_string "foo") == 3

let%test _ = match split (of_string "foo bar") 3 with
  | Some(b1, b2) -> equal b1 (of_string "foo") && equal b2 (of_string " bar")
  | _ -> false

let%test _ = match split (of_string "foo bar") 10 with
  | None -> true
  | _ -> false
