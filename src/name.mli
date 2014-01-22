(** Name scopes. *)

(** Program identifiers. *)
type name = Name of string

(** Data constructor identifiers. *)
type dname = DName of string

(** Label identifiers. *)
type lname = LName of string

(** Type identifiers. *)
type tname = TName of string

(** Convert a label to an identifier. *)
val name_of_label : lname -> name

(** Convert an identifier to an label. *)
val label_of_name : name -> lname

(** Transform a class name into an accepted ocaml type name. *)
val type_of_class : tname -> tname

(** Create the label of a superclass of a class definition. *)
val make_superclass_label : tname -> tname -> lname

(** Create the name of an instance constructor. *)
val make_instance_name : tname -> tname -> name
