module HM () = struct
  type id = string
  and level = int

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
  and let_decl = id * ann option * exp

  and texp =
    | TEBool of bool * ty
    | TEVar of id * ty
    | TEApp of texp * texp * ty
    | TELam of id * texp * ty
    | TERecord of id * trecord_lit * ty
    | TEProj of texp * id * ty
    | TEIf of texp * texp * texp * ty
    | TELet of tlet_decl * texp * ty
    | TELetRec of tlet_decl list * texp * ty

  and trecord_lit = (id * texp) list
  and tlet_decl = id * ann option * texp

  and ann =
    | AnnName of id
    | AnnTyVar of id
    | AnnArrow of ann * ann

  (* record type with nominal type *)
  and ty =
    | TBool
    | TRecord of id * record_ty
    | TVar of tv ref
    | QVar of id
    | TArrow of ty * ty

  and record_ty = (id * ty) list

  and tv =
    | Unbound of id * level
    | Link of ty

  and bind =
    | VarBind of ty
    | TypeBind of ty

  and env = (id * bind) list

  exception Undefined of string
  exception Expected of string
  exception MissingField of string
  exception DuplicateDefinition of string
  exception UnificationFailure of string
  exception OccursCheck

  let current_level = ref 1
  let enter_level () = incr current_level
  let leave_level () = decr current_level
  let gensym_counter = ref 0

  let fresh_unbound_var () =
    let n = !gensym_counter in
    incr gensym_counter;
    let tvar = "'" ^ string_of_int n in
    TVar (ref (Unbound (tvar, !current_level)))

  let ty_kind (ty : ty) =
    match ty with
    | TBool -> "TBool"
    | TRecord (_, _) -> "TRecord"
    | TVar _ -> "TVar"
    | QVar _ -> "QVar"
    | TArrow (_, _) -> "TArrow"

  let rec ty_string (ty : ty) =
    match ty with
    | TBool -> "TBool"
    | TRecord (id, flds) -> Printf.sprintf "%s{%s}" id (ty_fields flds)
    | TVar { contents = Link ty } ->
        Printf.sprintf "TVar(Link(%s))" (ty_string ty)
    | TVar { contents = Unbound (id, lvl) } ->
        Printf.sprintf "TVar(Unbound(%s,%d))" id lvl
    | QVar id -> Printf.sprintf "QVar(%s)" id
    | TArrow (f, d) -> ty_string f ^ " -> " ^ ty_string d

  and ty_fields (flds : record_ty) =
    flds
    |> List.map (fun (id, ty) -> id ^ ": " ^ ty_string ty)
    |> String.concat ", "

  let lookup_var_type name e =
    match List.assoc_opt name e with
    | Some (VarBind t) -> t
    | _ -> raise (Undefined (Printf.sprintf "variable %s not defined" name))

  let lookup_type name e =
    match List.assoc_opt name e with
    | Some (TypeBind t) -> t
    | _ -> raise (Undefined (Printf.sprintf "type %s not defined" name))

  let reify_ann env ann =
    match ann with
    | None -> fresh_unbound_var ()
    | Some ann ->
        let hm = Hashtbl.create 0 in
        let rec reify_ann' ann =
          match ann with
          | AnnName id ->
              (* Type name: Look it up in the environment. *)
              lookup_type id env
          | AnnTyVar id -> (
              match Hashtbl.find_opt hm id with
              | Some ty -> ty
              | None ->
                  let tv = fresh_unbound_var () in
                  Hashtbl.add hm id tv;
                  tv)
          | AnnArrow (from, dst) ->
              let from = reify_ann' from in
              let dst = reify_ann' dst in
              TArrow (from, dst)
        in
        reify_ann' ann

  let type_error expected got =
    Expected (Printf.sprintf "expected type %s, got %s" expected got)

  let missing_field field inside =
    MissingField (Printf.sprintf "missing field %s in %s" field inside)

  let duplicate_definition def =
    DuplicateDefinition (Printf.sprintf "duplicate definition of %s" def)

  let[@tail_mod_cons] rec zipWith f l1 l2 =
    match (l1, l2) with x :: xs, y :: ys -> f x y :: zipWith f xs ys | _ -> []

  let rec force : ty -> ty = function
    | TVar { contents = Link ty } -> force ty
    | ty -> ty

  let rec gen (ty : ty) : ty =
    match force ty with
    | TVar { contents = Unbound (id, lvl) } when lvl > !current_level ->
        (* Generalize this unbound type variable only if its level is deeper
           than our current level. That is, it doesn't appear in the
           environment. *)
        QVar id
    | TArrow (from, dst) ->
        (* Generalize the type vars in the parameter and return types. *)
        TArrow (gen from, gen dst)
    | TRecord (id, flds) ->
        (* Generalize the type vars in the record fields. *)
        let gen_fld (id, ty) = (id, gen ty) in
        TRecord (id, List.map gen_fld flds)
    | ty -> ty

  let inst (ty : ty) : ty =
    (* Use this hash table to keep track of polytypes that have already been
       instantiated. *)
    let tbl = Hashtbl.create 0 in
    let rec inst' (ty : ty) =
      match force ty with
      | QVar id -> (
          (* If it's a polytype, check to see if we've already instantiated
             it. *)
          match Hashtbl.find_opt tbl id with
          | Some tv -> tv
          | None ->
              (* Otherwise, create a fresh monotype, and add it into the
                 table. *)
              let tv = fresh_unbound_var () in
              Hashtbl.add tbl id tv;
              tv)
      | TArrow (from, dst) ->
          (* Instantiate the type vars in the parameter and return types. *)
          TArrow (inst' from, inst' dst)
      | TRecord (id, flds) ->
          (* Instantiate the type vars in the record fields. *)
          let inst_fld (id, ty) = (id, inst' ty) in
          TRecord (id, List.map inst_fld flds)
      | ty -> ty
    in
    inst' ty

  let rec occurs src ty =
    (* Follow all the links. If we see a type variable, it will only be
       Unbound. *)
    match force ty with
    | TVar tgt when src == tgt ->
        (* src type variable occurs in ty. *)
        raise OccursCheck
    | TVar tgt ->
        (* Grab src and tgt's levels. *)
        let (Unbound (_, src_lvl)) = !src in
        let (Unbound (id, tgt_lvl)) = !tgt in

        (* Compute the minimum of their levels (the outermost scope). *)
        let min_lvl = min src_lvl tgt_lvl in

        (* Update the tgt's level to be the minimum. *)
        tgt := Unbound (id, min_lvl)
    | TArrow (from, dst) ->
        (* Check that src occurs in the parameter and return type. *)
        occurs src from;
        occurs src dst
    | TRecord (_, flds) ->
        (* Check that src occurs in the field types. *)
        List.iter (fun (_, ty) -> occurs src ty) flds
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
    | _ when t1 == t2 -> () (* The types are trivially equal (e.g. TBool). *)
    | TVar tv, ty | ty, TVar tv ->
        (* If either type is a type variable, ensure that the type variable does
           not occur in the type. Update the levels while you're at it. *)
        occurs tv ty;

        (* Link the type variable to the type. *)
        tv := Link ty
    | TArrow (f1, d1), TArrow (f2, d2) ->
        (* If both types are function types, unify their parameters with each
           other and their return types with each other. *)
        unify f1 f2;
        unify d1 d2
    | TRecord (id1, fds1), TRecord (id2, fds2)
      when id1 == id2 && List.length fds1 == List.length fds2 ->
        (* Both types are records with the same name and number of fields. *)
        let unify_fld (id1, ty1) (id2, ty2) =
          if id1 <> id2 then raise (fail_unify ty1 ty2) else unify ty1 ty2
        in

        (* Unify their corresponding fields. *)
        List.iter2 unify_fld fds1 fds2
    | _ ->
        (* Unification has failed. *)
        raise (fail_unify t1 t2)

  let typ : texp -> ty = function
    | TEBool _ -> TBool
    | TEVar (_, ty) -> ty
    | TEApp (_, _, ty) -> ty
    | TELam (_, _, ty) -> ty
    | TERecord (_, _, ty) -> ty
    | TEProj (_, _, ty) -> ty
    | TEIf (_, _, _, ty) -> ty
    | TELet (_, _, ty) -> ty
    | TELetRec (_, _, ty) -> ty

  let rec infer (env : env) (exp : exp) : texp =
    match exp with
    | EBool b -> TEBool (b, TBool) (* A true/false value is of type Bool. *)
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
        let ty_arr = TArrow (typ arg, ty_res) in

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
        TELam (param, body, TArrow (ty_param, typ body))
    | ERecord (tname, rec_lit) ->
        (* TODO: annotated record types? *)
        (* Look up the declared type for the type name on the record literal. *)
        let ty_dec = lookup_type tname env in

        (* Infer the types of all the fields in the literal. *)
        let rec_lit = List.map (fun (id, x) -> (id, infer env x)) rec_lit in

        (* Synthesize a record type with the types of those fields. *)
        let ty_rec =
          TRecord (tname, List.map (fun (id, x) -> (id, typ x)) rec_lit)
        in

        (* Unify that with the declared type. *)
        unify ty_dec ty_rec;

        (* Return the record's type. *)
        TERecord (tname, rec_lit, ty_dec)
    | EProj (rcd, fld) -> (
        (* Infer the type of the expression we're projecting on. *)
        let rcd = infer env rcd in
        (* Check that it's actually a record. *)
        match typ rcd with
        | TRecord (name, rec_ty) -> (
            (* Check that it has the field we're accessing. *)
            match List.assoc_opt fld rec_ty with
            (* Return the field's type in the record. *)
            | Some ty -> TEProj (rcd, fld, ty)
            | _ -> raise (missing_field fld name))
        | ty -> raise (type_error "TRecord" (ty_kind ty)))
    | EIf (cond, thn, els) ->
        (* Check that the type of condition is Bool. *)
        let cond = infer env cond in
        unify (typ cond) TBool;

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

        (* If there's a type annotation on this let binding, reify it. *)
        let ty_rhs = reify_ann env ann in
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
        let deduped_defs : (id, unit) Hashtbl.t = Hashtbl.create 0 in

        (* Extend environment with the declarations in the recursive let binding
           and check for duplicates. *)
        let extend_env (id, ann, _) env' =
          match Hashtbl.find_opt deduped_defs id with
          | Some _ -> raise (duplicate_definition id)
          | None ->
              Hashtbl.add deduped_defs id ();
              (* If there's a type annotation, reify it. Fresh type variables
                 are instantiated at the current level. *)
              let ty_decl = reify_ann env ann in

              (* Extend the environment by prepending the binding and its
                 type. *)
              (id, VarBind ty_decl) :: env'
        in
        let env' = List.fold_right extend_env decls env in

        (* Using the extended environment, infer the types of the
           right-hand-side of all the let declarations. *)
        let infer_let (id, VarBind ty_bind) (_, ann, rhs) =
          let rhs = infer env' rhs in
          unify ty_bind (typ rhs);
          (id, ann, rhs)
        in
        let decls = zipWith infer_let env' decls in

        (* Decrement the nesting level after this recursive let binding. *)
        leave_level ();

        (* Generalize the types of all the bindings. Only type variables at a
           deeper level are generalized. *)
        let generalized_bindings =
          List.map (fun (id, _, rhs) -> (id, VarBind (gen (typ rhs)))) decls
        in

        (* Update the types in the environment by appending them to the original
           env.*)
        let env = List.append generalized_bindings env in

        (* Typecheck the body of the recursive let binding and return up its
           type. *)
        let body = infer env body in
        TELetRec (decls, body, typ body)
end

let%test "id" =
  let open HM () in
  let x = infer [] (ELet (("a", None, ELam ("x", EVar "x")), EVar "a")) in
  let t = typ x in
  print_endline (ty_string t);
  true

let%test "id2" =
  let open HM () in
  let x = infer [] (ELet (("a", None, ELam ("x", EVar "x")), EVar "a")) in
  let t = typ x in
  print_endline (ty_string t);
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
  print_endline (ty_string t);
  true
