open InferenceTypes
open MultiEquation
open Name



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

type implication = tname * tname list

let implications = ref []

(** [equivalent [b1;..;bN] k t [(k_1,t_1);...;(k_N,t_N)]] registers
    a rule of the form (E). *)
let equivalent bs k t kts = () (* TODO *)

(** [canonicalize pos pool c] where [c = [(k_1,t_1);...;(k_N,t_N)]]
    decomposes [c] into an equivalent constraint [c' =
    [(k'_1,v_1);...;(k'_M,v_M)]], introducing the variables
    [v_1;...;v_M] in [pool]. It raises [Unsat] if the given constraint
    is equivalent to [false]. *)
let canonicalize pos pool k =
  (* TODO expand as much as we can using (E) and (E'), but how do we work with variables? *)
  k

(** [add_implication k [k_1;...;k_N]] registers a rule of the form
    (E'). *)
let add_implication k ks =
  implications := (k, ks) :: !implications

(** [entails C1 C2] returns true is the canonical constraint [C1] implies
    the canonical constraint [C2]. *)
let entails c1 c2 =
  let entails_one cs c =
    true (* TODO *)
  in
  List.for_all (entails_one c1) c2


(** [contains k1 k2] *)
let contains k1 k2 =
  let rec rcontains k1 k2 =
    if k1 = k2 then true
    else
      try
        let (_, ks) = List.find (fun (k, _) -> k = k1) !implications in
        List.exists (fun k -> rcontains k k2) ks
      with Not_found -> false
  in
  rcontains k1 k2
