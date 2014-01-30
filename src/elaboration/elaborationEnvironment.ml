open Positions
open Name
open XAST
open Types
open ElaborationExceptions

type t = {
  values       : (tnames * binding) list;
  types        : (tname * (Types.kind * type_definition)) list;
  classes      : (tname * class_definition) list;
  labels       : (lname * (tnames * Types.t * tname)) list;
}

let empty = { values = []; types = []; classes = []; labels = [] }

let values env = env.values
let classes env = env.classes

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

(* Determine whether the class [k1] is a superclass of the class [k2]
   (noted k1 < k2 in the course book). *)
let rec is_superclass pos k1 k2 env =
  let super2 = lookup_superclasses pos k2 env in
  List.mem k1 super2 ||
  List.fold_left (fun b k -> if b then true else is_superclass pos k1 k env) false super2

(* Lookup a dictionary instance which can build a dictionary of type [k]. *)
let lookup_dinst (k,t) env =
  try
    Some (List.find (fun (ts, (x, ty)) ->
      match (destruct_ntyarrow ty, t) with
          ((_, TyApp (_, k0, [TyApp (_, g0, _)])),
           TyApp (_, g, _)) -> k = k0 && g = g0
        | _ -> false
    ) env.values)
  with Not_found -> None

(* Lookup a dictionary projection which can extract a dictionary of type [k]. *)
let lookup_dproj (k,t) env =
  List.filter (fun (ts, (x, t)) ->
    match destruct_tyarrow t with
      Some (
        TyApp (_, k0, [TyVar(_,a0)]),
        TyApp (_, k1,[TyVar(_,a1)])) -> k1 = k && a0 = a1
    | _ -> false
  ) env.values

(* Lookup a dictionary variable of type [k]. *)
let lookup_dvar (k,t) env =
  let t = TyApp (undefined_position, k, [t]) in
  try
    let (_, (x, _)) = List.find (fun (_, (x, ty)) -> equivalent t ty) env.values in
    Some x
  with Not_found -> None

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

