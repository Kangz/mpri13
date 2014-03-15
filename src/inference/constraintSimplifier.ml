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

type class_info = (tname * tname list * variable * (lname * crterm) list)
type instance_info = unit

type equivalence = variable list * (tname * variable) * (tname * variable) list

let classes = ref []
let instances = ref []


let add_class cli =
  classes := cli::(!classes)

let add_instance isi =
  instances := isi::(!instances)

let lookup_class c =
  try
    List.find (fun (c', _, _, _) -> c = c') !classes
  with Not_found -> raise (UnboundClass c)



(** [canonicalize pos pool c] where [c = [(k_1,t_1);...;(k_N,t_N)]]
    decomposes [c] into an equivalent constraint [c' =
    [(k'_1,v_1);...;(k'_M,v_M)]], introducing the variables
    [v_1;...;v_M] in [pool]. It raises [Unsat] if the given constraint
    is equivalent to [false]. *)
let canonicalize pos pool cs =
  let finished = ref false in
  let expand cs =
    List.fold_left (fun cs (k,t) ->
      try
        let (_, ks, _, _) = lookup_class k in
        finished := true;
        if ks == [] then [k,t] @ cs
        else (List.map (fun k -> (k,t)) ks) @ cs
      with Not_found -> (k,t)::cs
    ) [] cs
  in
  let rec expand_all cs =
    finished := false;
    let cs = expand cs in
    if !finished then cs
    else expand_all cs
  in
  let unique cs =
    List.fold_left (fun cs (k, t) ->
      if List.mem (k,t) cs then cs else (k,t)::cs) [] cs
  in

  (* Apply implications as much as possible. *)
  let cs = unique (expand_all cs) in

  (* TODO Contract the produced context, using equivalences. *)
(*  List.iter (fun (k, v) -> introduce pool v) cs; *)
  cs

(** [entails C1 C2] returns true is the canonical constraint [C1] implies
    the canonical constraint [C2]. *)
let rec entails c1 c2 =
  let entails_one cs (k, a) =
    List.exists (fun (k', a') ->
      if a = a' then contains k' k
      else false
    ) cs
  in
  List.for_all (entails_one c1) c2


(** [contains k1 k2] *)
and contains k1 k2 =
  if k1 = k2 then true
  else
    try
      let (_,ks,_,_) = lookup_class k1 in
      List.exists (fun k -> contains k k2) ks
    with Not_found -> false

