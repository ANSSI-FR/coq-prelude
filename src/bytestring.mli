type t

val of_list : char list -> t
val of_string : string -> t
val to_string : t -> string
val case : (char -> t -> 'a) -> (unit -> 'a) -> t -> 'a
val unpack : t -> (char * t) option
val pack : (char * t) -> t
val empty : t
val append : t -> t -> t
val length : t -> int
val equal : t -> t -> bool
val bytestring_of_int : int -> t
val int_of_bytestring : t -> int option
val split : t -> int -> (t * t) option
val read_line : unit -> t
val print_bytestring : t -> unit
