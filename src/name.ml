type name = Name of string

type dname = DName of string

type lname = LName of string

type tname = TName of string

let name_of_label (LName s) = Name s ;;
let label_of_name (Name s) = LName s ;;
let type_of_class (TName s) = TName ("c" ^ s) ;;

(* Create the field name of a superclass of a class definition. *)
let make_superclass_label (TName k) (TName super) = LName (k ^ super) ;;

(* Create the name of the instance constructor. *)
let make_instance_name (TName k) (TName g) = Name (k ^ "_" ^ g) ;;

