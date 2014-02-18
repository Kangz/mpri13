open String
open Name
open XAST
open Types
open Positions
open ElaborationErrors
open ElaborationExceptions
open ElaborationEnvironment

let string_of_type ty      = ASTio.(XAST.(to_string pprint_ml_type ty))
let is_canonical pos ts context env =
  List.iter (fun (ClassPredicate (k1, a1)) ->
    List.iter (fun (ClassPredicate (k2, a2)) ->
      if k1 != k2 &&
         a1 = a2 &&
         List.mem a1 ts &&
         is_superclass pos k1 k2 env then
        raise (TheseTwoClassesMustNotBeInTheSameContext (pos, k1, k2));
    ) context
  ) context
;;


let rec program p = handle_error List.(fun () ->
  flatten (fst (Misc.list_foldmap block ElaborationEnvironment.initial p))
)

and block env = function
  | BTypeDefinitions ts ->
    let env = type_definitions env ts in
    ([BTypeDefinitions ts], env)

  | BDefinition d ->
    let d, env = value_binding env d in
    ([BDefinition d], env)

  | BClassDefinition c ->
    let pos = c.class_position in

    (* The function [bind_class] already checks for existing defintions of
       [c]. *)

    (* Check the independance of the superclasses.
       Since this check must find the list of superclasses
       of each of [c.superclasses], their existance is checked
       at the same time. *)
    List.iter (fun k1 ->
      List.iter (fun k2 ->
        if k1 != k2 && is_superclass pos k1 k2 env then
          raise (TheseTwoClassesMustNotBeInTheSameContext (pos, k1, k2));
      ) c.superclasses
    ) c.superclasses;

    (* Build the record type definition corresponding to the class. *)
    let ckind = KArrow (KStar, KStar)
    and cname = type_of_class c.class_name
    and cparam = c.class_parameter in
    let crecords =
      (List.map (fun k ->
        (pos, make_superclass_label cname k, TyApp (pos, type_of_class k, [TyVar (pos, cparam)]))
      ) c.superclasses) @ c.class_members in
    let ctype = TypeDef (pos, ckind, cname, DRecordType ([cparam], crecords)) in

    (* Build the class members. *)
    let cmembers = List.map (fun (pos, lname, typ) ->
      let name = name_of_label lname in
      (* Check that [lname] is not bound. *)
      if is_bound name env then
        raise (OverloadedSymbolCannotBeBound (pos, name));

      (* The type [K a]. *)
      let ka = TyApp (pos, cname, [TyVar (pos, cparam)]) in
      ValueDef (pos,
        [cparam],
        [],
        (name, TyApp (pos, TName "->", [ka; typ])),
        EForall (pos, [cparam],
          ELambda (pos,
            (Name "_z", ka),
            ERecordAccess (pos, EVar (pos, Name "_z", []), lname))))
    ) crecords in

    (* Bind. *)
    let env = type_definitions env (TypeDefs (pos, [ctype])) in
    let (def, env) = block env (BDefinition (BindValue (pos, cmembers))) in
    let env = bind_class c.class_name c env in
    (BTypeDefinitions (TypeDefs (pos, [ctype])) :: def, env)

  | BInstanceDefinitions is ->
    (* Do some checks, and build the different environments needed for the elaboration. *)
    let (envs, env) = List.fold_left (fun (envs, env) i ->
      let pos = i.instance_position in
      let cname = type_of_class i.instance_class_name in
      let g = i.instance_index in
      let context = i.instance_typing_context in
      let context_arg = List.map (
        fun (ClassPredicate (k,a)) -> TyApp (pos, type_of_class k, [TyVar (pos, a)])
      ) context in

      (* Check the canonicity of the typing context of [i]. *)
      is_canonical pos i.instance_parameters context env;

      (* The index [i.instance_index] must be a datatype constructor of arity
         the size of [i.instance_parameters]. *)
      let k = lookup_type_kind pos g env in
      let params = List.map (fun p -> TyVar (pos, p)) i.instance_parameters in
      if g = TName "->" then raise (IllKindedType pos);
      check_type_constructor_application pos env k params;

      (* Bind the instance constructor in the environment. *)
      let iname = make_instance_name cname g in
      let ityp = ntyarrow pos context_arg (TyApp (pos, cname, [TyApp (pos, g, params)])) in
      let nenv = bind_scheme iname i.instance_parameters ityp env in

      ((env, (iname, ityp)) :: envs, nenv)
    ) ([], env) is in

    (* At this point, [env] contains all the instance constructors. *)

    (* Elaborate the class members. *)
    let decls = List.map2 (fun (penv, (iname, ityp)) i ->
      let pos = i.instance_position in
      let cname = type_of_class i.instance_class_name in
      let c = lookup_class pos i.instance_class_name env in
      let g = i.instance_index in
      let context = i.instance_typing_context in
      let context_arg = List.map (
        fun (ClassPredicate (k,a)) -> TyApp (pos, type_of_class k, [TyVar (pos, a)])
      ) context in
      let params = List.map (fun p -> TyVar (pos, p)) i.instance_parameters in

      (* Create the needed dictionaries. *)
      let karg = List.mapi (fun i _ -> Name ("_z" ^ string_of_int i)) context in
      let with_context env = List.fold_left2 (
        fun env z t -> bind_simple z t env
      ) (introduce_type_parameters env i.instance_parameters) karg context_arg in

      (* Create the records corresponding to the superclasses. *)
      let records =
        (* The superclasses (elaborated in the partial environment). *)
        List.map (fun k ->
          let q = elaborate_dictionary (with_context penv) (pos, type_of_class k, TyApp (pos, g, params)) in
          RecordBinding (make_superclass_label cname k, q)
        ) c.superclasses @
        (* The methods. *)
        List.map (fun (RecordBinding (u,e)) ->
          (* Restrict the environment if needed. *)
          let renv = match e with
              ELambda _ -> with_context env
            | _ -> with_context penv
          in
          (* Elaborate the expression. *)
          let (e, t) = expression renv e in

          (* Match the type with that from the class definition. *)
          let (ts, texp, _) = lookup_label pos u renv in
          let texp = substitute (List.combine ts [TyApp (pos, g, params)]) texp in
          check_equal_types pos t texp;
          RecordBinding (u,e)) i.instance_members in

      let ibuilder =
        EForall (pos, i.instance_parameters,
          List.fold_right2 (fun z t e -> ELambda (pos, (z, t), e)) karg context_arg
            (ERecordCon (pos, Name "", [], records)))
      in
      ValueDef (pos, i.instance_parameters, [], (iname, ityp), ibuilder)
    ) (List.rev envs) is in

    ([BDefinition (BindRecValue (undefined_position, decls))], env)

and elaborate_dictionary env (pos, tname, typ) =
  (* Lookup dict variables. *)
  match lookup_dvar (tname, typ) env with
    Some x -> EVar (pos, x, [])
  | None ->
    try
      (* Lookup dict instances. *)
      match (lookup_dinst (tname, typ) env, typ) with
        (Some (ts, (x, ty)), TyApp (_,_,typarg))  ->
          let (ity, oty) = destruct_ntyarrow ty in
          let darg = List.map (fun ity ->
            match ity with
              TyApp (_, k, [aty]) ->
                (* Elaboration of the instance arguments. *)
                elaborate_dictionary env (pos, k, aty)
            | _ -> raise (CannotElaborateDictionary (pos, ity))
          ) ity in
          List.fold_left (fun e f -> EApp (pos, e, f)) (EVar (pos, x, typarg)) darg
      | _ -> raise (CannotElaborateDictionary (pos, TyApp (pos, tname, [typ])))
    (* Either no instance found, or error in the elaboration of the instance arguments. *)
    with CannotElaborateDictionary _ ->
      begin
        (* Lookup dict proj.
           Each projection is tested until the right one is found. *)
        let ans = List.fold_left (fun ans (ts, (x, t)) ->
          match (ans, destruct_tyarrow t) with
            (Some _, _) -> ans
          | (None, Some (TyApp (pos, k0, [_]), _)) ->
            begin try
              let e0 = elaborate_dictionary env (pos, k0, typ) in
              Some (EApp (pos, (EVar (pos, x, [typ])), e0))
            with CannotElaborateDictionary _ -> None
            end
          | _ -> None
        ) None (lookup_dproj (tname, typ) env) in
        match ans with
          Some e -> e
        | None -> raise (CannotElaborateDictionary (pos, TyApp (pos, tname, [typ])))
      end

and type_definitions env (TypeDefs (_, tdefs)) =
  let env = List.fold_left env_of_type_definition env tdefs in
  List.fold_left type_definition env tdefs

and env_of_type_definition env = function
  | (TypeDef (pos, kind, t, _)) as tdef ->
    bind_type t kind tdef env

  | (ExternalType (p, ts, t, os)) as tdef ->
    bind_type t (kind_of_arity (List.length ts)) tdef env

and type_definition env = function
  | TypeDef (pos, _, t, dt) -> datatype_definition t env dt
  | ExternalType (p, ts, t, os) -> env

and datatype_definition t env = function
  | DAlgebraic ds ->
    List.fold_left algebraic_dataconstructor env ds
  | DRecordType (ts, ltys) ->
    List.fold_left (label_type ts t) env ltys

and label_type ts rtcon env (pos, l, ty) =
  let env' = List.fold_left (fun env x -> bind_type_variable x env) env ts in
  check_wf_type env' KStar ty;
  bind_label pos l ts ty rtcon env

and algebraic_dataconstructor env (_, DName k, ts, kty) =
  check_wf_scheme env ts kty;
  bind_scheme (Name k) ts kty env

and introduce_type_parameters env ts =
  List.fold_left (fun env t -> bind_type_variable t env) env ts

and check_wf_scheme env ts ty =
  check_wf_type (introduce_type_parameters env ts) KStar ty

and check_wf_type env xkind = function
  | TyVar (pos, t) ->
    let tkind = lookup_type_kind pos t env in
    check_equivalent_kind pos xkind tkind

  | TyApp (pos, t, tys) ->
    let kt = lookup_type_kind pos t env in
    check_type_constructor_application pos env kt tys

and check_type_constructor_application pos env k tys =
  match tys, k with
  | [], KStar -> ()
  | ty :: tys, KArrow (k, ks) ->
    check_wf_type env k ty;
    check_type_constructor_application pos env ks tys
  | _ ->
    raise (IllKindedType pos)

and check_equivalent_kind pos k1 k2 =
  match k1, k2 with
    | KStar, KStar -> ()
    | KArrow (k1, k2), KArrow (k1', k2') ->
      check_equivalent_kind pos k1 k1';
      check_equivalent_kind pos k2 k2'
    | _ ->
      raise (IncompatibleKinds (pos, k1, k2))

and env_of_bindings env cdefs = List.(
  (function
    | BindValue (_, vs)
    | BindRecValue (_, vs) ->
      fold_left (fun env (ValueDef (_, ts, _, (x, ty), _)) ->
        bind_scheme x ts ty env
      ) env vs
    | ExternalValue (_, ts, (x, ty), _) ->
      bind_scheme x ts ty env
  ) cdefs
)

and check_equal_types pos ty1 ty2 =
  if not (equivalent ty1 ty2) then
    raise (IncompatibleTypes (pos, ty1, ty2))

and type_application pos env x tys =
  List.iter (check_wf_type env KStar) tys;
  let (ts, (_, ty)) = lookup pos x env in
  try
    substitute (List.combine ts tys) ty
  with _ ->
    raise (InvalidTypeApplication pos)

and expression env = function
  | EVar (pos, ((Name s) as x), tys) ->
    let t = type_application pos env x tys in
    let (ity, oty) = destruct_ntyarrow t in
    let (darg, arg) = List.partition (fun ty ->
      match ty with
        TyApp (_, s, _) -> is_class_name s env
      | _ -> false
    ) ity in
    let darg = List.map (fun t ->
      match t with
        TyApp (pos, k, [ty]) -> elaborate_dictionary env (pos, k, ty)
      | _ -> raise (CannotElaborateDictionary (pos, t))
    ) darg in
    let e = List.fold_left (fun e f -> EApp (pos, e, f)) (EVar (pos, x, tys)) darg in
    (e, ntyarrow pos arg oty)

  | ELambda (pos, ((x, aty) as b), e') ->
    check_wf_type env KStar aty;
    let env = bind_simple x aty env in
    let (e, ty) = expression env e' in
    (ELambda (pos, b, e), ntyarrow pos [aty] ty)

  | EApp (pos, a, b) ->
    let a, a_ty = expression env a in
    let b, b_ty = expression env b in
    begin match destruct_tyarrow a_ty with
      | None ->
        raise (ApplicationToNonFunctional pos)
      | Some (ity, oty) ->
        check_equal_types pos b_ty ity;
        (EApp (pos, a, b), oty)
    end

  | EBinding (pos, vb, e) ->
    let vb, env = value_binding env vb in
    let e, ty = expression env e in
    (EBinding (pos, vb, e), ty)

  | EForall (pos, tvs, e) ->
    (** Because type abstractions are removed by [value_binding]. *)
    raise (OnlyLetsCanIntroduceTypeAbstraction pos)

  | ETypeConstraint (pos, e, xty) ->
    let e, ty = expression env e in
    check_equal_types pos ty xty;
    (e, ty)

  | EExists (_, _, e) ->
    (** Because we are explicitly typed, flexible type variables
        are useless. *)
    expression env e

  | EDCon (pos, DName x, tys, es) ->
    let ty = type_application pos env (Name x) tys in
    let (itys, oty) = destruct_ntyarrow ty in
    if List.(length itys <> length es) then
      raise (InvalidDataConstructorApplication pos)
    else
      let es =
        List.map2 (fun e xty ->
          let (e, ty) = expression env e in
          check_equal_types pos ty xty;
          e
        ) es itys
      in
      (EDCon (pos, DName x, tys, es), oty)

  | EMatch (pos, s, bs) ->
    let (s, sty) = expression env s in
    let bstys = List.map (branch env sty) bs in
    let bs = fst (List.split bstys) in
    let tys = snd (List.split bstys) in
    let ty = List.hd tys in
    List.iter (check_equal_types pos ty) (List.tl tys);
    (EMatch (pos, s, bs), ty)

  | ERecordAccess (pos, e, l) ->
    let e, ty = expression env e in
    let (ts, lty, rtcon) = lookup_label pos l env in
    let ty =
      match ty with
        | TyApp (_, r, args) ->
          if rtcon <> r then
            raise (LabelDoesNotBelong (pos, l, r, rtcon))
          else
            begin try
              let s = List.combine ts args in
              Types.substitute s lty
            with _ ->
              (** Because we only well-kinded types and only store
                  well-kinded types in the environment. *)
              assert false
            end
        | _ ->
          raise (RecordExpected (pos, ty))
    in
    (ERecordAccess (pos, e, l), ty)

  | ERecordCon (pos, n, i, []) ->
    (** We syntactically forbids empty records. *)
    assert false

  | ERecordCon (pos, n, i, rbs) ->
    let rbstys = List.map (record_binding env) rbs in
    let rec check others rty = function
      | [] ->
        List.rev others, rty
      | (RecordBinding (l, e), ty) :: ls ->
        if List.exists (fun (RecordBinding (l', _)) -> l = l') others then
          raise (MultipleLabels (pos, l));

        let (ts, lty, rtcon) = lookup_label pos l env in
        let (s, rty) =
          match rty with
            | None ->
              let rty = TyApp (pos, rtcon, i) in
              let s =
                try
                  List.combine ts i
                with _ -> raise (InvalidRecordInstantiation pos)
              in
              (s, rty)
            | Some (s, rty) ->
              (s, rty)
        in
        check_equal_types pos ty (Types.substitute s lty);
        check (RecordBinding (l, e) :: others) (Some (s, rty)) ls
    in
    let (ls, rty) = check [] None rbstys in
    let rty = match rty with
      | None -> assert false
      | Some (_, rty) -> rty
    in
    (ERecordCon (pos, n, i, ls), rty)

  | ((EPrimitive (pos, p)) as e) ->
    (e, primitive pos p)

and primitive pos = function
  | PIntegerConstant _ ->
    TyApp (pos, TName "int", [])

  | PUnit ->
    TyApp (pos, TName "unit", [])

  | PCharConstant _ ->
    TyApp (pos, TName "char", [])

and branch env sty (Branch (pos, p, e)) =
  let denv = pattern env sty p in
  let env = concat pos env denv in
  let (e, ty) = expression env e in
  (Branch (pos, p, e), ty)

and concat pos env1 env2 =
  List.fold_left
    (fun env (_, (x, ty)) -> bind_simple x ty env)
    env1 (values env2)

and linear_bind pos env (ts, (x, ty)) =
  assert (ts = []); (** Because patterns only bind monomorphic values. *)
  try
    ignore (lookup pos x env);
    raise (NonLinearPattern pos)
  with UnboundIdentifier _ ->
    bind_simple x ty env

and join pos denv1 denv2 =
  List.fold_left (linear_bind pos) denv2 (values denv1)

and check_same_denv pos denv1 denv2 =
  List.iter (fun (ts, (x, ty)) ->
    assert (ts = []); (** Because patterns only bind monomorphic values. *)
    try
      let (_, (_, ty')) = lookup pos x denv2 in
      check_equal_types pos ty ty'
    with _ ->
      raise (PatternsMustBindSameVariables pos)
  ) (values denv1)

and pattern env xty = function
  | PVar (_, name) ->
    bind_simple name xty ElaborationEnvironment.empty

  | PWildcard _ ->
    ElaborationEnvironment.empty

  | PAlias (pos, name, p) ->
    linear_bind pos (pattern env xty p) ([], (name, xty))

  | PTypeConstraint (pos, p, pty) ->
    check_equal_types pos pty xty;
    pattern env xty p

  | PPrimitive (pos, p) ->
    check_equal_types pos (primitive pos p) xty;
    ElaborationEnvironment.empty

  | PData (pos, (DName x), tys, ps) ->
    let kty = type_application pos env (Name x) tys in
    let itys, oty = destruct_ntyarrow kty in
    if List.(length itys <> length ps) then
      raise (InvalidDataConstructorApplication pos)
    else
      let denvs = List.map2 (pattern env) itys ps in (
        check_equal_types pos oty xty;
        List.fold_left (join pos) ElaborationEnvironment.empty denvs
      )

  | PAnd (pos, ps) ->
    List.fold_left
      (join pos)
      ElaborationEnvironment.empty
      (List.map (pattern env xty) ps)

  | POr (pos, ps) ->
    let denvs = List.map (pattern env xty) ps in
    let denv = List.hd denvs in
    List.(iter (check_same_denv pos denv) (tl denvs));
    denv

and record_binding env (RecordBinding (l, e)) =
  let e, ty = expression env e in
  (RecordBinding (l, e), ty)

and value_binding env = function
  | BindValue (pos, vs) ->
    let (vs, env) = Misc.list_foldmap value_definition env vs in
    (BindValue (pos, vs), env)

  | BindRecValue (pos, vs) ->
    let env = List.fold_left value_declaration env vs in
    let (vs, _) = Misc.list_foldmap value_definition env vs in
    (BindRecValue (pos, vs), env)

  | ExternalValue (pos, ts, ((x, ty) as b), os) ->
    let env = bind_scheme x ts ty env in
    (ExternalValue (pos, ts, b, os), env)

and eforall pos ts e =
  match ts, e with
    | ts, EForall (pos, [], ((EForall _) as e)) ->
      eforall pos ts e
    | [], EForall (pos, [], e) ->
      e
    | [], EForall (pos, _, _) ->
      raise (InvalidNumberOfTypeAbstraction pos)
    | [], e ->
      e
    | x :: xs, EForall (pos, t :: ts, e) ->
      if x <> t then
        raise (SameNameInTypeAbstractionAndScheme pos);
      eforall pos xs (EForall (pos, ts, e))
    | _, _ ->
      raise (InvalidNumberOfTypeAbstraction pos)


and value_definition env (ValueDef (pos, ts, ps, (x, xty), e)) =
  let env = introduce_type_parameters env ts in
  if is_overloaded (label_of_name x) env then
    raise (OverloadedSymbolCannotBeBound (pos, x));
  check_wf_scheme env ts xty;
  (* The variables used in the class predicates must be defined in [xty]. *)
  let ftv = type_variables xty in
  if List.exists (fun (ClassPredicate (k, ty)) -> not (List.mem ty ftv)) ps then
    raise (InvalidOverloading pos);

  if is_value_form e then begin
    (* Check the canonicity of the typing context. *)
    is_canonical pos ts ps env;
    (* Check the number of type abstractions. *)
    let e = eforall pos ts e in
    (* The class predicates are transformed into arguments. *)
    let psn = List.mapi (fun i _ -> Name ("_z" ^ string_of_int i)) ps in
    let e = List.fold_right2 (fun (ClassPredicate (k, t)) z e ->
      ELambda (pos, (z, TyApp (pos, type_of_class k, [TyVar (pos, t)])), e)) ps psn e in
    let e, ty = expression env e in
    (* Modify the type [xty] to match that of the modified expression [e]. *)
    let xty = List.fold_right (fun (ClassPredicate (k,ty)) t ->
      ntyarrow pos [TyApp (pos, type_of_class k, [TyVar (pos, ty)])] t
    ) ps xty in
    check_equal_types pos xty ty;
    (ValueDef (pos, ts, [], (x, ty), EForall (pos, ts, e)),
     bind_scheme x ts ty env)
  end else begin
    (* If the expression is not in value form, the class constraints are ignored. *)
    if ts <> [] || ps <> [] then
      raise (ValueRestriction pos)
    else
      let e = eforall pos [] e in
      let e, ty = expression env e in
      let b = (x, ty) in
      check_equal_types pos xty ty;
      (ValueDef (pos, [], [], b, e), bind_simple x ty env)
  end

and value_declaration env (ValueDef (pos, ts, ps, (x, ty), e)) =
  (* The type needs to be transformed to include the class predicates. *)
  let ty = List.fold_right (fun (ClassPredicate (k,t)) ty ->
    ntyarrow pos [TyApp (pos, type_of_class k, [TyVar (pos, t)])] ty
  ) ps ty in
  bind_scheme x ts ty env


and is_value_form = function
  | EVar _
  | ELambda _
  | EPrimitive _ ->
    true
  | EDCon (_, _, _, es) ->
    List.for_all is_value_form es
  | ERecordCon (_, _, _, rbs) ->
    List.for_all (fun (RecordBinding (_, e)) -> is_value_form e) rbs
  | EExists (_, _, t)
  | ETypeConstraint (_, t, _)
  | EForall (_, _, t) ->
    is_value_form t
  | _ ->
    false

