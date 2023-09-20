open Base

module HM () = struct
  type id = string
  and level = int
  and prog = tycon list * exp

  and tycon = {
    name : id;
    type_params : id list;
    ty : record_ty;
  }

  and exp =
    | EBool of bool
    | EVar of id
    | EApp of exp * exp
    | ELam of id * exp
    | ERecord of id * record_lit
    | EProj of exp * id
    | EIf of exp * exp * exp
    | ELet of let_decl * exp
    | ELetRec of let_decl list * exp

  and record_lit = (id * exp) list
  and let_decl = id * ty option * exp

  and texp =
    | TEBool of bool * ty
    | TEVar of id * ty
    | TEApp of texp * texp * ty
    | TELam of id * texp * ty
    | TERecord of id * tyrecord_lit * ty
    | TEProj of texp * id * ty
    | TEIf of texp * texp * texp * ty
    | TELet of tlet_decl * texp * ty
    | TELetRec of tlet_decl list * texp * ty

  and tyrecord_lit = (id * texp) list
  and tlet_decl = id * ty option * texp

  and ty =
    | TyBool
    | TyRecord of id * record_ty
    | TyVar of tv ref
    | QVar of id
    | TyArrow of ty * ty
    | TyName of id
    | TyApp of ty * ty

  and record_ty = (id * ty) list

  and tv =
    | Unbound of id * level
    | Link of ty

  and bind =
    | VarBind of ty
    | TypeBind of tycon

  and env = (id * bind) list

  exception Undefined of string
  exception Expected of string
  exception MissingField of string
  exception DuplicateDefinition of string
  exception UnificationFailure of string
  exception OccursCheck

  let current_level = ref 1
  let enter_level () = Int.incr current_level
  let leave_level () = Int.decr current_level
  let gensym_counter = ref 0

  let fresh_unbound_var () =
    let n = !gensym_counter in
    Int.incr gensym_counter;
    let tvar = "'" ^ Int.to_string n in
    TyVar (ref (Unbound (tvar, !current_level)))

  let ty_kind (ty : ty) =
    match ty with
    | TyBool -> "TyBool"
    | TyRecord _ -> "TyRecord"
    | QVar _ -> "QVar"
    | TyVar _ -> "TyVar"
    | TyArrow _ -> "TyArrow"
    | TyName _ -> "TyName"
    | TyApp _ -> "TyApp"

  let rec ty_string (ty : ty) =
    match ty with
    | TyBool -> "TyBool"
    | TyRecord (id, flds) -> Printf.sprintf "%s{%s}" id (ty_fields flds)
    | TyVar { contents = Link ty } ->
        Printf.sprintf "TyVar(Link(%s))" (ty_string ty)
    | TyVar { contents = Unbound (id, lvl) } ->
        Printf.sprintf "TyVar(Unbound(%s,%d))" id lvl
    | QVar id -> Printf.sprintf "QVar(%s)" id
    | TyArrow (f, d) -> ty_string f ^ " -> " ^ ty_string d
    | TyName name -> name
    | TyApp (ty, param) ->
        Printf.sprintf "%s %s" (ty_string ty) (ty_string param)

  and ty_fields (flds : record_ty) =
    flds
    |> List.map ~f:(fun (id, ty) -> id ^ ": " ^ ty_string ty)
    |> String.concat ~sep:", "

  let lookup_var_type name (e : env) : ty =
    match List.Assoc.find e ~equal:Poly.equal name with
    | Some (VarBind t) -> t
    | _ -> raise (Undefined (Printf.sprintf "variable %s not defined" name))

  let lookup_tycon name (e : env) : tycon =
    match List.Assoc.find e ~equal:Poly.equal name with
    | Some (TypeBind t) -> t
    | _ -> raise (Undefined (Printf.sprintf "type %s not defined" name))

  let type_error expected got =
    Expected (Printf.sprintf "expected type %s, got %s" expected got)

  let missing_field field inside =
    MissingField (Printf.sprintf "missing field %s in %s" field inside)

  let duplicate_definition def =
    DuplicateDefinition (Printf.sprintf "duplicate definition of %s" def)

  let[@tail_mod_cons] rec zipWith f l1 l2 =
    match (l1, l2) with x :: xs, y :: ys -> f x y :: zipWith f xs ys | _ -> []

  let rec force : ty -> ty = function
    | TyVar { contents = Link ty } -> force ty
    | ty -> ty

  let rec gen (ty : ty) : ty =
    (* let type_params : id Hash_set.t = Hash_set.create (module String) in *)
    match force ty with
    | TyVar { contents = Unbound (id, lvl) } when lvl > !current_level ->
        (* Generalize this unbound type variable only if its level is deeper
           than our current level. That is, it doesn't appear in the
           environment. *)
        QVar id
    | TyArrow (from, dst) ->
        (* Generalize the type vars in the parameter and return types. *)
        (* gen' from; gen' dst *)
        TyArrow (gen from, gen dst)
    | TyApp (a, b) ->
        (* gen' a; gen' b *)
        TyApp (gen a, gen b)
    | TyRecord (id, flds) ->
        (* Generalize the type vars in the record fields. *)
        let gen_fld (id, ty) = (id, gen ty) in
        TyRecord (id, List.map ~f:gen_fld flds)
    | ty -> ty

  let inst ?tbl (pty : ty) : ty =
    let tbl =
      match tbl with None -> Hashtbl.create (module String) | Some tbl -> tbl
    in
    let rec inst' (ty : ty) =
      match force ty with
      | QVar id -> (
          match Hashtbl.find tbl id with
          | Some tv -> tv
          | None ->
              (* Otherwise, create a fresh monotype, and add it into the
                 table. *)
              let tv = fresh_unbound_var () in
              Hashtbl.add_exn tbl ~key:id ~data:tv;
              tv)
      | TyArrow (from, dst) ->
          (* Instantiate the type vars in the parameter and return types. *)
          TyArrow (inst' from, inst' dst)
      | TyApp (a, b) -> TyApp (inst' a, inst' b)
      | TyRecord (id, flds) ->
          (* Instantiate the type vars in the record fields. *)
          let inst_fld (id, ty) = (id, inst' ty) in
          TyRecord (id, List.map ~f:inst_fld flds)
      | ty -> ty
    in
    let ty = inst' pty in
    ty

  let expect_varbind bind =
    match bind with VarBind ty -> ty | _ -> failwith "expected VarBind"

  let expect_unbound (tv : tv ref) =
    match !tv with
    | Unbound (id, lvl) -> (id, lvl)
    | _ -> failwith "expected Unbound"

  let rec occurs (src : tv ref) (ty : ty) : unit =
    (* Follow all the links. If we see a type variable, it will only be
       Unbound. *)
    match force ty with
    | TyVar tgt when phys_equal src tgt ->
        (* src type variable occurs in ty. *)
        raise OccursCheck
    | TyVar tgt ->
        (* Grab src and tgt's levels. *)
        let _, src_lvl = expect_unbound src in
        let id, tgt_lvl = expect_unbound tgt in
        (* Compute the minimum of their levels (the outermost scope). *)
        let min_lvl = min src_lvl tgt_lvl in
        (* Update the tgt's level to be the minimum. *)
        tgt := Unbound (id, min_lvl)
    | TyArrow (from, dst) ->
        (* Check that src occurs in the parameter and return type. *)
        occurs src from;
        occurs src dst
    | TyApp (a, b) ->
        occurs src a;
        occurs src b (* TODO: this is correct right? *)
    | TyRecord (_, flds) ->
        (* Check that src occurs in the field types. *)
        List.iter ~f:(fun (_, ty) -> occurs src ty) flds
    | _ -> ()

  let fail_unify t1 t2 =
    UnificationFailure
      (Printf.sprintf "failed to unify type %s with %s" (ty_string t1)
         (ty_string t2))

  let rec unify (t1 : ty) (t2 : ty) : unit =
    (* Follow all the links. If we see any type variables, they will only be
       Unbound. *)
    let t1, t2 = (force t1, force t2) in
    match (t1, t2) with
    | _ when Poly.equal t1 t2 ->
        () (* The types are trivially equal (e.g. TyBool). *)
    | TyVar tv, ty | ty, TyVar tv ->
        (* If either type is a type variable, ensure that the type variable does
           not occur in the type. Update the levels while you're at it. *)
        occurs tv ty;
        (* Link the type variable to the type. *)
        tv := Link ty
    | TyArrow (f1, d1), TyArrow (f2, d2) ->
        (* If both types are function types, unify their parameters with each
           other and their return types with each other. *)
        unify f1 f2;
        unify d1 d2
    | TyRecord (id1, fds1), TyRecord (id2, fds2)
      when Poly.equal id1 id2
           && Poly.equal (List.length fds1) (List.length fds2) ->
        (* Both types are records with the same name and number of fields. *)
        let unify_fld (id1, ty1) (id2, ty2) =
          let (_ : id) = id1 in
          if not (Poly.equal id1 id2) then raise (fail_unify ty1 ty2)
          else unify ty1 ty2
        in
        (* Unify their corresponding fields. *)
        List.iter2_exn ~f:unify_fld fds1 fds2
    | TyApp (a1, b1), TyApp (a2, b2) ->
        unify a1 a2;
        unify b1 b2
    | TyName a, TyName b when Poly.equal a b -> ()
    | _ ->
        (* Unification has failed. *)
        raise (fail_unify t1 t2)

  let typ : texp -> ty = function
    | TEBool _ -> TyBool
    | TEVar (_, ty) -> ty
    | TEApp (_, _, ty) -> ty
    | TELam (_, _, ty) -> ty
    | TERecord (_, _, ty) -> ty
    | TEProj (_, _, ty) -> ty
    | TEIf (_, _, _, ty) -> ty
    | TELet (_, _, ty) -> ty
    | TELetRec (_, _, ty) -> ty

  (* Returns the the tyname/tyapp, as well as underlying type instantiated with
     those fresh unbound vars. *)
  let inst_tycon (tc : tycon) : ty * ty =
    (* Fold over tc.type_params and build up a tyapp, while also adding to a
       hash table. Then, instantiate the type with the hash table. *)
    let tbl = Hashtbl.create (module String) in
    let tyapp =
      List.fold_right tc.type_params ~init:(TyName tc.name) ~f:(fun id acc ->
          let tv = fresh_unbound_var () in
          Hashtbl.add_exn tbl ~key:id ~data:tv;
          TyApp (acc, tv))
    in
    (tyapp, inst ~tbl (TyRecord (tc.name, tc.ty)))

  let rec infer (env : env) (exp : exp) : texp =
    match exp with
    | EBool b -> TEBool (b, TyBool) (* A true/false value is of type Bool. *)
    | EVar name ->
        (* Variable is being used. Look up its type in the environment, *)
        let var_ty = lookup_var_type name env in
        (* instantiate its type by replacing all of its quantified type
           variables with fresh unbound type variables.*)
        TEVar (name, inst var_ty)
    | EApp (fn, arg) ->
        (* To typecheck a function application, first infer the types of the
           function and the argument. *)
        let fn = infer env fn in
        let arg = infer env arg in
        (* Instantiate a fresh type variable for the result of the application,
           and synthesize an arrow type going from the argument to the
           result. *)
        let ty_res = fresh_unbound_var () in
        let ty_arr = TyArrow (typ arg, ty_res) in
        (* Unify it with the function's type. *)
        unify (typ fn) ty_arr;
        (* Return the result type. *)
        TEApp (fn, arg, ty_res)
    | ELam (param, body) ->
        (* Instantiate a fresh type variable for the lambda parameter, and
           extend the environment with the param and its type. *)
        let ty_param = fresh_unbound_var () in
        let env' = (param, VarBind ty_param) :: env in
        (* Typecheck the body of the lambda with the extended environment. *)
        let body = infer env' body in
        (* Return a synthesized arrow type from the parameter to the body. *)
        TELam (param, body, TyArrow (ty_param, typ body))
    | ERecord (tname, rec_lit) ->
        (* TODO: annotated record types? *)
        (* Look up the declared type for the type name on the record literal. *)
        let tcon = lookup_tycon tname env in
        let ty_app, ty_dec = inst_tycon tcon in
        (* let (ty_dec, tyvars) = inst pty in (* oof but tyvars needs to be ordered *) *)
        (* order the type vars based on their order in the lookup? *)
        (* let tyvars = List.map pty.type_params ~f:(fun id -> Hashtbl.find_exn
           tyvars id) in *)
        (* let ty_app = tyapp_from_vars (TyName(tname)) tyvars in *)
        (* Infer the types of all the fields in the literal. *)
        let rec_lit = List.map ~f:(fun (id, x) -> (id, infer env x)) rec_lit in
        (* Synthesize a record type with the types of those fields. *)
        let ty_rec =
          TyRecord (tname, List.map ~f:(fun (id, x) -> (id, typ x)) rec_lit)
        in
        (* Unify that with the declared type. *)
        unify ty_dec ty_rec;
        (* Return the record's type. *)
        TERecord (tname, rec_lit, ty_app)
    | EProj (rcd, fld) -> (
        (* Infer the type of the expression we're projecting on. *)
        let rcd = infer env rcd in
        (* Check that it's actually a record. *)
        match typ rcd with
        | TyRecord (name, rec_ty) -> (
            (* Check that it has the field we're accessing. *)
            match List.Assoc.find rec_ty ~equal:Poly.equal fld with
            (* Return the field's type in the record. *)
            | Some ty -> TEProj (rcd, fld, ty)
            | _ -> raise (missing_field fld name))
        | ty -> raise (type_error "TyRecord" (ty_kind ty)))
    | EIf (cond, thn, els) ->
        (* Check that the type of condition is Bool. *)
        let cond = infer env cond in
        unify (typ cond) TyBool;
        (* Check that the types of the branches are equal to each other. *)
        let thn = infer env thn in
        let els = infer env els in
        unify (typ thn) (typ els);
        (* Return the type of one of the branches. (we'll pick the "then"
           branch) *)
        TEIf (cond, thn, els, typ thn)
    | ELet ((id, ann, rhs), body) ->
        (* Increment the nesting level at this let binding. *)
        enter_level ();
        (* If there's a type annotation on this let binding, instantiate it. *)
        let ty_rhs =
          match ann with Some ann -> inst ann | None -> fresh_unbound_var ()
        in
        (* Infer the type of the right-hand-side. *)
        let rhs = infer env rhs in
        (* Unify it with the annotated type. *)
        unify ty_rhs (typ rhs);
        (* Decrement the nesting level after this let binding. *)
        leave_level ();
        (* Generalize the type of the inferred binding, and it to our
           environment. Only type variables at a deeper level are
           generalized. *)
        let ty_gen = gen ty_rhs in
        let env = (id, VarBind ty_gen) :: env in
        (* Typecheck the body of the let binding and return up its type. *)
        let body = infer env body in
        TELet ((id, ann, rhs), body, typ body)
    | ELetRec (decls, body) ->
        (* Increment the nesting level at this recursive let binding. *)
        enter_level ();
        (* Use this hash table to keep track of duplicate definitions in the
           recursive let. *)
        let deduped_defs : (id, unit) Hashtbl.t =
          Hashtbl.create (module String)
        in
        (* Extend environment with the declarations in the recursive let binding
           and check for duplicates. *)
        let extend_env (id, ann, _) env' =
          match Hashtbl.find deduped_defs id with
          | Some _ -> raise (duplicate_definition id)
          | None ->
              Hashtbl.add_exn deduped_defs ~key:id ~data:();
              (* If there's a type annotation, reify it. Fresh type variables
                 are instantiated at the current level. *)
              let ty_decl =
                match ann with
                | Some ann -> inst ann
                | None -> fresh_unbound_var ()
              in

              (* Extend the environment by prepending the binding and its
                 type. *)
              (id, VarBind ty_decl) :: env'
        in
        let env' : env = List.fold_right ~f:extend_env ~init:env decls in
        (* Using the extended environment, infer the types of the
           right-hand-side of all the let declarations. *)
        let infer_let (id, bind) (_, ann, rhs) =
          let ty_bind = expect_varbind bind in
          let rhs = infer env' rhs in
          unify ty_bind (typ rhs);
          (* It's safe to do .ty because ty_bind is not generalized. *)
          (id, ann, rhs)
        in
        let decls = zipWith infer_let env' decls in
        (* Decrement the nesting level after this recursive let binding. *)
        leave_level ();
        (* Generalize the types of all the bindings. Only type variables at a
           deeper level are generalized. *)
        let generalized_bindings =
          List.map ~f:(fun (id, _, rhs) -> (id, VarBind (gen (typ rhs)))) decls
        in
        (* Update the types in the environment by appending them to the original
           env.*)
        let env = List.append generalized_bindings env in
        (* Typecheck the body of the recursive let binding and return up its
           type. *)
        let body = infer env body in
        TELetRec (decls, body, typ body)

  let checkTycon m tc =
    let m = Hash_set.copy m in
    List.iter tc.type_params ~f:(fun id -> Hash_set.add m id);
    let rec checkTycon' ty =
      match ty with
      | TyVar _ -> failwith "checkTycon: TyVar"
      | TyArrow (from, dst) ->
          checkTycon' from;
          checkTycon' dst
      | TyApp (a, b) ->
          checkTycon' a;
          checkTycon' b
      | TyRecord (tname, flds) ->
          if not (Hash_set.mem m tname) then
            raise (Undefined (Printf.sprintf "type %s not defined" tname));
          List.iter flds ~f:(fun (_, ty) -> checkTycon' ty)
      | TyName tname ->
          if not (Hash_set.mem m tname) then
            raise (Undefined (Printf.sprintf "type %s not defined" tname))
      | _ -> ()
    in
    checkTycon' (TyRecord (tc.name, tc.ty))

  let typecheck_prog (tl, exp) =
    let m = Hash_set.create (module String) in
    let env =
      List.fold_right tl ~init:[] ~f:(fun tc acc ->
          Hash_set.add m tc.name;
          (tc.name, TypeBind tc) :: acc)
    in
    (* walk tycons again to make sure that all tynames are referenced *)
    List.iter tl ~f:(checkTycon m);
    infer env exp
end

let%test "id" =
  let open HM () in
  let x = infer [] (ELet (("a", None, ELam ("x", EVar "x")), EVar "a")) in
  let t = typ x in
  Stdio.print_endline (ty_string t);
  true

let%test "id2" =
  let open HM () in
  let x = infer [] (ELet (("a", None, ELam ("x", EVar "x")), EVar "a")) in
  let t = typ x in
  Stdio.print_endline (ty_string t);
  true

let%test "fix" =
  let open HM () in
  let x =
    ELetRec
      ( [
          ("fix", None, ELam ("f", EApp (EVar "f", EApp (EVar "fix", EVar "f"))));
        ],
        EVar "fix" )
  in
  let x = infer [] x in
  let t = typ x in
  Stdio.print_endline (ty_string t);
  true

let%test "tdecl" =
  let open HM () in
  let prog =
    ( [ { name = "Foo"; type_params = [ "'a" ]; ty = [ ("x", QVar "'a") ] } ],
      ERecord ("Foo", [ ("x", EBool true) ]) )
  in
  let x = typecheck_prog prog in
  let t = typ x in
  Stdio.print_endline (ty_string t);
  true
