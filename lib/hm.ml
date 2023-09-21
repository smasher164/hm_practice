open Base

(** Module HM contains a typechecker for the Damas-Hindley-Milner (DHM) type
    system with some basic extensions like nominal records, type annotations, and
    recursive let bindings. It uses unification based on union-find (Algorithm J)
    to solve type constraints. *)
module HM () = struct
  (* Represents identifiers like variables, type names, and type variables. *)
  type id = string

  (* The level is an integer counter that holds the depth of the current scope.
     Every unbound type variable contains the level at which it was created. *)
  type level = int

  (* An expression *)
  type exp =
    | EBool of bool (* boolean: true/false *)
    | EVar of id (* variable: x *)
    | EApp of exp * exp (* function application: f arg *)
    | ELam of id * exp (* lambda: fun x -> x *)
    | ERecord of id * record_lit (* record literal: Foo{x = true, y = false} *)
    | EProj of exp * id (* record projection: r.y *)
    | EIf of
        exp
        * exp
        * exp (* if-then-else: if <cond-exp> then <then-exp> else <else-exp> *)
    | ELet of let_decl * exp
      (* let binding: let x : <type-annotation> = <rhs-exp> in <body-exp> *)
    | ELetRec of
        let_decl list
        * exp (* recursive let binding: let rec <decls> in <body-exp> *)

  and record_lit = (id * exp) list
  and let_decl = id * ty option * exp

  (* A typed expression *)
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

  (* A type *)
  and ty =
    | TyBool (* Bool *)
    | TyRecord of id * record_ty (* Record: Foo{x: Bool, y: Bool} *)
    | TyVar of tv ref
      (* Type variable Unbound/Link. Held behind a mutable reference. *)
    | QVar of id
      (* Quantified type variable. If a type T contains a QVar("'a"), it implies
         that T is a polytype of the with an implicit forall 'a in front of it.
         For example, TyArrow(QVar("'a"), TyBool) is equivalent to forall 'a. 'a
         -> Bool *)
    | TyArrow of ty * ty (* Function type: T1 -> T2 *)
    | TyName of id (* Type name: Foo *)
    | TyApp of ty * ty (* Type application: T1 T2 *)

  and record_ty = (id * ty) list

  and tv =
    | Unbound of id * level
      (* Unbound type variable: Holds the type variable's name as well as the
         level at which it was created. *)
    | Link of ty (* Link type variable: Holds a reference to a type. *)

  (* Type declaration/constructor. All type declarations are nominal records. *)
  and tycon = {
    name : id;
    type_params : id list;
    ty : record_ty;
  }

  (* A program is a list of type declarations and an expression to be
     evaluated. *)
  and prog = tycon list * exp

  and bind =
    | VarBind of ty (* A variable binding maps to the variable's type. *)
    | TypeBind of tycon (* A type binding maps to a type constructor. *)

  (* The environment is a list of bindings. *)
  and env = (id * bind) list

  (* Utility functions for pretty printing. *)
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

  and tycon_string (tc : tycon) =
    Printf.sprintf "type %s %s = %s" tc.name (ty_fields tc.ty)
      (ty_string (TyRecord (tc.name, tc.ty)))

  and ty_fields (flds : record_ty) =
    flds
    |> List.map ~f:(fun (id, ty) -> id ^ ": " ^ ty_string ty)
    |> String.concat ~sep:", "

  (* The typechecker raises the following exceptions. *)
  exception Undefined of string
  exception Expected of string
  exception MissingField of string
  exception DuplicateDefinition of string
  exception UnificationFailure of string
  exception OccursCheck

  let undefined_error kind name =
    Undefined (Printf.sprintf "%s %s not defined" kind name)

  let type_error expected got =
    Expected (Printf.sprintf "expected type %s, got %s" expected got)

  let missing_field field inside =
    MissingField (Printf.sprintf "missing field %s in %s" field inside)

  let duplicate_definition def =
    DuplicateDefinition (Printf.sprintf "duplicate definition of %s" def)

  let unify_failed t1 t2 =
    UnificationFailure
      (Printf.sprintf "failed to unify type %s with %s" (ty_string t1)
         (ty_string t2))

  let expect_varbind bind =
    match bind with VarBind ty -> ty | _ -> failwith "expected VarBind"

  let expect_unbound (tv : tv ref) =
    match !tv with
    | Unbound (id, lvl) -> (id, lvl)
    | _ -> failwith "expected Unbound"

  (* Lookup a variable's type in the environment. *)
  let lookup_var_type name (e : env) : ty =
    match List.Assoc.find e ~equal:Poly.equal name with
    | Some (VarBind t) -> t
    | _ -> raise (undefined_error "variable" name)

  (* Lookup a type constructor in the environment. *)
  let lookup_tycon name (e : env) : tycon =
    match List.Assoc.find e ~equal:Poly.equal name with
    | Some (TypeBind t) -> t
    | _ -> raise (undefined_error "type" name)

  (* Get the type of a typed expression. *)
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

  (* Zip over two lists, and apply a function to each pair of elements. If the
     lists have different lengths, stop at the shorter length. *)
  let[@tail_mod_cons] rec zipWith f l1 l2 =
    match (l1, l2) with x :: xs, y :: ys -> f x y :: zipWith f xs ys | _ -> []

  (* Global state that stores the current level and a counter for generating
     fresh unbound type variables. *)
  let current_level = ref 1
  let enter_level () = Int.incr current_level
  let leave_level () = Int.decr current_level
  let gensym_counter = ref 0

  (* Generate a fresh unbound type variable. *)
  let fresh_unbound_var () =
    let n = !gensym_counter in
    Int.incr gensym_counter;
    let tvar = "'" ^ Int.to_string n in
    TyVar (ref (Unbound (tvar, !current_level)))

  (* Dereference a type variable by following all the links and get the
     underlying type. *)
  let rec force : ty -> ty = function
    | TyVar { contents = Link ty } -> force ty
    | ty -> ty

  (* Generalize a type by replacing all the unbound type variables with
     quantified type variables. In order to decide whether to generalize an
     unbound type variable, we just check if its level is deeper than the
     current scope, i.e. the scope containing the let binding. *)
  let rec gen (ty : ty) : ty =
    match force ty with
    | TyVar { contents = Unbound (id, lvl) } when lvl > !current_level ->
        (* Generalize this unbound type variable only if its level is deeper
           than our current level. That is, it doesn't appear in the
           environment. *)
        QVar id
    | TyArrow (from, dst) ->
        (* Generalize the type vars in the parameter and return types. *)
        TyArrow (gen from, gen dst)
    | TyApp (a, b) ->
        (* Generalize the type vars in the type application. *)
        TyApp (gen a, gen b)
    | TyRecord (id, flds) ->
        (* Generalize the type vars in the record fields. *)
        let gen_fld (id, ty) = (id, gen ty) in
        TyRecord (id, List.map ~f:gen_fld flds)
    | ty -> ty

  (* Instantiate a polytype by replacing all the quantified type variables with
     fresh unbound type variables. Ensure that the same type variable ID gets
     mapped to the same unbound type variable by using a (id, ty) Hashtbl. *)
  let inst ?tbl (pty : ty) : ty =
    let tbl =
      (* If a hash table is provided, use it. Otherwise, create a new one. *)
      match tbl with None -> Hashtbl.create (module String) | Some tbl -> tbl
    in
    let rec inst' (ty : ty) =
      match force ty with
      | QVar id -> (
          (* If we see a quantified type variable, check if it's in the hash
             table. *)
          match Hashtbl.find tbl id with
          | Some tv -> tv (* If it is, return the type variable. *)
          | None ->
              (* Otherwise, create a fresh monotype, and add it into the
                 table. *)
              let tv = fresh_unbound_var () in
              Hashtbl.add_exn tbl ~key:id ~data:tv;
              tv)
      | TyArrow (from, dst) ->
          (* Instantiate the type vars in the parameter and return types. *)
          TyArrow (inst' from, inst' dst)
      | TyApp (a, b) ->
          (* Instantiate the type vars in the type application. *)
          TyApp (inst' a, inst' b)
      | TyRecord (id, flds) ->
          (* Instantiate the type vars in the record fields. *)
          let inst_fld (id, ty) = (id, inst' ty) in
          TyRecord (id, List.map ~f:inst_fld flds)
      | ty -> ty
    in
    inst' pty

  (* Instantiate a type constructor into a type with fresh unbound vars. Returns
     the underlying record type for unifying with a record literal, as well as a
     TyName or TyApp for returning in infer. *)
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

  (* Occurs check: check if a type variable occurs in a type. If it does, raise
     an exception. Otherwise, update the type variable's level to be the minimum
     of its current level and the type's level. *)
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
        occurs src b
    | TyRecord (_, flds) ->
        (* Check that src occurs in the field types. *)
        List.iter ~f:(fun (_, ty) -> occurs src ty) flds
    | _ -> ()

  (* Unify two types. If they are not unifiable, raise an exception. *)
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
          if not (Poly.equal id1 id2) then raise (unify_failed ty1 ty2)
          else unify ty1 ty2
        in
        (* Unify their corresponding fields. *)
        List.iter2_exn ~f:unify_fld fds1 fds2
    | TyApp (a1, b1), TyApp (a2, b2) ->
        unify a1 a2;
        unify b1 b2
    | TyName a, TyName b when Poly.equal a b ->
        () (* The type names are the same. *)
    | _ ->
        (* Unification has failed. *)
        raise (unify_failed t1 t2)

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
        (* Look up the declared type constructor for the type name on the record
           literal. *)
        let tcon = lookup_tycon tname env in
        (* Instantiate the type constructor into a type with fresh unbound
           variables. It returns both a type application representation as well
           as the underlying record type. *)
        let ty_app, ty_dec = inst_tycon tcon in
        (* Infer the types of all the fields in the literal. *)
        let rec_lit = List.map ~f:(fun (id, x) -> (id, infer env x)) rec_lit in
        (* Synthesize a record type with the types of those fields. *)
        let ty_rec =
          TyRecord (tname, List.map ~f:(fun (id, x) -> (id, typ x)) rec_lit)
        in
        (* Unify that with the declared type. *)
        unify ty_dec ty_rec;
        (* Return the the type application representation. *)
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
        (* Generalize the type of the inferred binding, and add it to our
           environment. Only type variables at a deeper level are
           generalized. *)
        let ty_gen = gen ty_rhs in
        let env = (id, VarBind ty_gen) :: env in
        (* Typecheck the body of the let binding and return up its type. *)
        let body = infer env body in
        TELet ((id, ann, rhs), body, typ body)
    | ELetRec (decls, body) ->
        (* To typecheck recursive let bindings, delay generalization until after
           each let binding is inferred. *)
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
              (* If there's a type annotation, instantiate it. Fresh type
                 variables are instantiated at the current level. *)
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
        let infer_let : id * bind -> let_decl -> id * ty option * texp =
         fun (id, bind) (_, ann, rhs) ->
          let ty_bind = expect_varbind bind in
          let rhs = infer env' rhs in
          unify ty_bind (typ rhs);
          (* It's safe to do .ty because ty_bind is not generalized. *)
          (id, ann, rhs)
        in
        (* We use zip here to map over the environment and the corresponding let
           declaration at the same time. This lets us access and typecheck the
           right-hand-side of a let binding. *)
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

  (* Walk a type constructor and make sure any type names or qvars it references
     actually exist. There should be no type variables (unbound/link) in a type
     constructor, since it hasn't instantiated into a type yet. *)
  let checkTycon names tc =
    let names = Hash_set.copy names in
    List.iter tc.type_params ~f:(fun id -> Hash_set.add names id);
    let rec checkTycon' ty =
      match ty with
      | TyVar _ -> failwith "unexpected: TyVar"
      | TyArrow (from, dst) ->
          checkTycon' from;
          checkTycon' dst
      | TyApp (a, b) ->
          checkTycon' a;
          checkTycon' b
      | TyRecord (tname, flds) ->
          if not (Hash_set.mem names tname) then
            raise (undefined_error "type" tname);
          List.iter flds ~f:(fun (_, ty) -> checkTycon' ty)
      | TyName tname ->
          if not (Hash_set.mem names tname) then
            raise (undefined_error "type" tname)
      | TyBool -> ()
      | QVar id ->
          if not (Hash_set.mem names id) then raise (undefined_error "type" id)
    in
    checkTycon' (TyRecord (tc.name, tc.ty))

  (* Typecheck a program. *)
  let typecheck_prog (tl, exp) =
    let m = Hash_set.create (module String) in
    (* Do an initial pass over type declarations to check for duplicates and add
       their names to a Hash_set for checking their definitions. Also add these
       bindings to an environment that can be passed to infer. *)
    let env =
      List.fold_right tl ~init:[] ~f:(fun tc acc ->
          (match Hash_set.strict_add m tc.name with
          | Ok () -> ()
          | Error _ -> raise (duplicate_definition tc.name));
          (tc.name, TypeBind tc) :: acc)
    in
    (* Walk tycons again to make sure that all type names and qvars are
       referenced. *)
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
