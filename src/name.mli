(** Name scopes. *)

(** Program identifiers. *)
type name = Name of string

(** Data constructor identifiers. *)
type dname = DName of string

(** Label identifiers. *)
type lname = LName of string

(** Type identifiers. *)
type tname = TName of string

(* Convert a label to an identifier. *)
val name_of_label : lname -> name
