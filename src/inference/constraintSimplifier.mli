(** This module implements reasoning about canonical constraints of the form:

    K_1 T_1 /\ ... K_N T_N

    using rules of the form:

    - forall b_1 ... b_N, k t ≡ k_1 t_1 /\ ... k_N t_N   (E)
    - forall b, k b => k_1 b /\ ... k_N b                (E')
*)

open Positions
open Name
open MultiEquation

(** [Unsat] is raised if a canonical constraint C ≡ false. *)
exception Unsat

(** [OverlappingInstances] is raised if two rules of kind (E) overlap. *)
exception OverlappingInstances of tname * variable

(** [MultipleClassDefinitions k] is raised if two rules of kind (I)
    share the same goal. *)
exception MultipleClassDefinitions of tname

(** [UnboundClass k] is raised if the type class [k] occurs in a
    constraint while it is undefined. *)
exception UnboundClass of tname

type class_info = (tname * tname list * variable * (lname * crterm) list)
type instance_info = unit

(** [add_class c] records a class definition. *)
val add_class : class_info -> unit
(** [add_instance i] records an instance definition. *)
val add_instance : instance_info -> unit

(** [lookup_class c] lookups up the defintion of the class [c]. *)
val lookup_class : tname -> class_info

(** [canonicalize pos pool c] where [c = [(k_1,t_1);...;(k_N,t_N)]]
    decomposes [c] into an equivalent constraint [c' =
    [(k'_1,v_1);...;(k'_M,v_M)]], introducing the variables
    [v_1;...;v_M] in [pool]. It raises [Unsat] if the given constraint
    is equivalent to [false]. *)
val canonicalize
  : position -> pool -> (tname * variable) list -> (tname * variable) list

(** [entails C1 C2] returns true is the canonical constraint [C1] implies
    the canonical constraint [C2]. *)
val entails
  : (tname * variable) list -> (tname * variable) list -> bool

(** [contains k1 k2] *)
val contains
  : tname -> tname -> bool
