open Positions
open Name
open XAST
open Types
open ElaborationExceptions

(* The type of dictionary constructors. *)
type dvar = binding * tname * Types.t list
and dinst = binding * tname list * (tname * tname list) list * (tname * (tname * tname list) list)
and dproj = binding * tname list * (tname * tname list) * (tname * tname list)

type t = {
  values       : (tnames * binding) list;
  types        : (tname * (Types.kind * type_definition)) list;
  classes      : (tname * class_definition) list;
  labels       : (lname * (tnames * Types.t * tname)) list;

  dprojs       : dproj list;
  dinsts       : dinst list
}

(* Type used to describe the arguments of a class predicate, in the function [elaborate_dictionary].
 * [Rigid t] means that the argument of the built dictionary has to be of type [t].
 * [Flexible v] means that the type is left unspecified. *)
type targ = Rigid of Types.t | Flexible of tname

let empty = { values = []; types = []; classes = []; labels = []; dprojs = []; dinsts = [] }

let values env = env.values
let classes env = env.classes
let dinsts env = env.dinsts

let is_overloaded x env =
  List.exists (fun (_, c) ->
    List.exists (fun (_ , x', _) -> x = x') c.class_members
  ) env.classes

let is_bound x env =
  List.exists (fun (_, (x', _)) -> x = x') env.values

let is_class_name s env =
  let c = class_of_type s in
  List.exists (fun (c', _) -> c = c') env.classes

let lookup pos x env =
  try
    List.find (fun (_, (x', _)) -> x = x') env.values
  with Not_found -> raise (UnboundIdentifier (pos, x))

let bind_scheme x ts ty env =
  { env with values = (ts, (x, ty)) :: env.values }

let bind_simple x ty env =
  bind_scheme x [] ty env

let bind_dproj p env =
  { env with dprojs = p::env.dprojs }
let bind_dinst ins env =
  { env with dinsts = ins::env.dinsts }

let bind_type t kind tdef env =
  { env with types = (t, (kind, tdef)) :: env.types }

let lookup_type pos t env =
  try
    List.assoc t env.types
  with Not_found ->
    raise (UnboundTypeVariable (pos, t))

let lookup_type_kind pos t env =
  fst (lookup_type pos t env)

let lookup_type_definition pos t env =
  snd (lookup_type pos t env)

let lookup_class pos k env =
  try
    List.assoc k env.classes
  with Not_found -> raise (UnboundClass (pos, k))

let bind_class k c env =
  try
    let pos = c.class_position in
    ignore (lookup_class pos k env);
    raise (AlreadyDefinedClass (pos, k))
  with UnboundClass _ ->
    { env with classes = (k, c) :: env.classes }

let lookup_superclasses pos k env =
  (lookup_class pos k env).superclasses

(* Determine whether the class [k1] (with the arguments [ty1]) is a superclass of the class
 * [k2] (with the arguments [ty2]. *)
let rec is_superclass pos (k1,ty1) (k2,ty2) env =
  let c2 = lookup_class pos k2 env in
  let renaming = List.combine c2.class_parameters ty2 in
  let super2 = List.map
    (fun (k, tys) -> (k, List.map (fun t -> List.assoc t renaming) tys)) c2.superclasses
  in
  (* Check direct ancestry. *)
  try
    let ty1' = List.assoc k1 super2 in
    if ty1 = ty1' then true
    else raise Not_found
  with
    (* Not a direct superclass, recursive check. *)
    Not_found ->
      List.fold_left (fun b (k, tys) ->
        if b then true else is_superclass pos (k1, ty1) (k, tys) env) false super2

(* Return [true] iff the two lists match on the elements that are not [None]. *)
let eqopt tys otys =
  List.for_all2 (fun t ot ->
    match ot with
      Flexible _ -> true
    | Rigid t' -> equivalent t t') tys otys

(* Bind the flexible variables to types of the second list. *)
let bindopt =
  List.fold_left2 (fun bind ot t ->
    match ot with
      Flexible v -> (v,t)::bind
    | Rigid _ -> bind) []


(* Return the list of types corresponding to the given variables. *)
let ntyvar =
  List.map (fun t -> TyVar (undefined_position, t))

(* Lookup a dictionary instance which can build a dictionary of type [k]. *)
let lookup_dinst (k,otys) env =
  List.fold_left (fun ans (((x, ty), ts, context, (k', indexes)) as inst) ->
    if k = k' then
      begin try
        let bind = List.fold_left2 (fun b (g, tys) ot ->
          match ot with
            Rigid (TyApp (_, g', _)) when g = g' -> b
          | Flexible v ->
            let ty = TyApp (undefined_position, g, ntyvar tys) in
            (v,ty)::b
          | _ -> raise Not_found
        ) [] indexes otys in
        (inst, bind)::ans
      with Not_found -> ans
      end
    else
      ans
  ) [] env.dinsts

(* Lookup a dictionary projection which can extract a dictionary of type [k]. *)
let lookup_dproj (k,otys) env =
  List.fold_left (fun ans (((x, t), ts, (k0,ty0), (k1,ty1)) as p) ->
    if k1 = k then
      (p, bindopt otys (ntyvar ty1))::ans
    else ans
  ) [] env.dprojs

(* Lookup a dictionary variable of type [k]. *)
let lookup_dvar (k,otys) env =
  List.fold_left (fun ans (ts, (x, ty)) ->
    match (ts, ty) with
      ([], TyApp (pos, k', tys)) when k = k' && eqopt tys otys ->
        (((x,ty),k,tys),bindopt otys tys)::ans
    | _ -> ans
  ) [] env.values

let bind_type_variable t env =
  bind_type t KStar (TypeDef (undefined_position, KStar, t, DAlgebraic [])) env

let lookup_label pos l env =
  try
    List.assoc l env.labels
  with Not_found ->
    raise (UnboundLabel (pos, l))

let bind_label pos l ts ty rtcon env =
  try
    ignore (lookup_label pos l env);
    raise (LabelAlreadyTaken (pos, l))
  with UnboundLabel _ ->
    { env with labels = (l, (ts, ty, rtcon)) :: env.labels }

let initial =
  let primitive_type t k = TypeDef (undefined_position, k, t, DAlgebraic []) in
  List.fold_left (fun env (t, k) ->
    bind_type t k (primitive_type t k) env
  ) empty [
    (TName "->", KArrow (KStar, KArrow (KStar, KStar)));
    (TName "int", KStar);
    (TName "char", KStar);
    (TName "unit", KStar)
  ]

let string_of_type ty      = ASTio.(XAST.(to_string pprint_ml_type ty))

let print_values env =
  List.iter (fun (_,(Name x, typ)) ->
    print_string (x ^ ": " ^ string_of_type typ ^ "\n")
  ) env.values

