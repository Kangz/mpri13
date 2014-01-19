type name = Name of string

type dname = DName of string

type lname = LName of string

type tname = TName of string

(* Convert a label to an identifier. *)
let name_of_label (LName s) = Name s ;;
