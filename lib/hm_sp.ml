open Base
open Poly

(* Module HM_SP contains a typechecker for the Damas-Hindley-Milner (DHM) type
   system with single-parameter typeclasses. *)
module HM_SP () = struct
  (* Represents identifiers like variables, type names, and type variables. *)
  type id = string

  (* The level is an integer counter that holds the depth of the current scope.
     Every unbound type variable contains the level at which it was created. *)
  type level = int

  (* An expression *)
  type exp =
    | EBool of bool (* true/false *)
    | EVar of id (* x *)
    | EApp of exp * exp (* f arg *)
    | ELam of id * exp (* fun x -> x *)
    | ERecord of id * record_lit (* Foo{x = true, y = false} *)
    | EProj of exp * id (* r.y *)
    | EIf of exp * exp * exp (* if <exp> then <exp> else <exp> *)
    | ELet of let_decl * exp (* let x : <type-annotation> = <exp> in <exp> *)
    | ELetRec of let_decl list * exp (* let rec <decls> in <exp> *)

  and record_lit = (id * exp) list
  and let_decl = id * qty option * exp

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
  and tlet_decl = id * qty option * texp

  (* A Quantified type. Should be read as forall p1..pn. ty, where p1..pn are
     the type parameters. It is separated from ty because in HM, a forall can
     only be at the top level of a type. *)
  and qty = {
    type_params : id list;
    (* Add constraints *)
    constraints : pred list;
    ty : ty;
  }

  (* ("Show", TyName "'a") *)
  and pred = id * ty
  and constraint_set = (id, id Hash_set.t) Hashtbl.t

  (* A type *)
  and ty =
    | TyBool (* Bool *)
    | TyRecord of id * record_ty (* Record: Foo{x: Bool, y: Bool} *)
    | TyVar of tv ref (* Type variable: held behind a mutable reference. *)
    | TyArrow of ty list (* Function type: T1 -> T2 *)
    | TyName of id (* Type name: Foo *)
    | TyApp of ty list (* Type application: T1 T2 *)

  and record_ty = (id * ty) list

  (* A type variable *)
  and tv =
    | Unbound of id * level
      (* Unbound type variable: Holds the type variable's name as well as the
         level at which it was created. *)
    | Link of ty (* Link type variable: Holds a reference to a type. *)

  (* Type declaration/constructor. All type declarations are nominal records. *)
  type tycon = {
    name : id;
    type_params : id list;
    constraints : pred list;
    ty : record_ty;
  }

  type instance_decl = qty * record_lit

  type trait_decl = {
    name : id;
    type_param : id;
    (* TODO: add superclass constraints *)
    def : record_ty;
    instances : instance_decl list;
  }

  (* TODO: instance predicates *)

  (* trait_name : id; qty : qty; *)

  (* body : record_lit; } *)

  (* Maps a type variable to a list of trait predicates. *)
  (* type pred = { tbl : (id, id list) Hashtbl.t } *)

  (* Maps a trait name to a list of types implementing it. *)
  (* type impl = { tbl : (id, (ty, instance_decl) Hashtbl.t) Hashtbl.t } *)
  type impl = { tbl : (id, qty list) Hashtbl.t }

  (* A program is a list of type declarations and an expression to be
     evaluated. *)
  type prog = {
    tycons : tycon list;
    traits : trait_decl list;
    body : exp;
  }

  type bind =
    | VarBind of qty (* A variable binding maps to a quantified type. *)
    | TypeBind of tycon (* A type binding maps to a type constructor. *)
    | TraitBind of trait_decl (* I think a trait_decl is best here? *)

  (* The environment is a list of bindings. *)
  type env = (id * bind) list

  (* Dereference a type variable by following all the links and get the
     underlying type. *)
  let rec force (ty : ty) : ty =
    match ty with
    | TyVar { contents = Link ty } -> force ty
    | ty -> ty

  (* Utility functions for pretty printing. *)
  let ty_kind (ty : ty) =
    match ty with
    | TyBool -> "TyBool"
    | TyRecord _ -> "TyRecord"
    | TyVar _ -> "TyVar"
    | TyArrow _ -> "TyArrow"
    | TyName _ -> "TyName"
    | TyApp _ -> "TyApp"

  let ty_fields f flds =
    flds
    |> List.map ~f:(fun (id, ty) -> id ^ ": " ^ f ty)
    |> String.concat ~sep:", "

  let ty_params = String.concat ~sep:" "

  (* TODO: print type params *)
  let tycon_string f (tc : tycon) =
    Printf.sprintf "type %s %s = %s" tc.name (ty_fields f tc.ty)
      (f (TyRecord (tc.name, tc.ty)))

  let pred_string f (id, ty) : string = id ^ " " ^ f ty

  let constraints f pl =
    if List.is_empty pl then ""
    else String.concat ~sep:", " (List.map pl ~f:(pred_string f)) ^ " => "

  let foralls tp =
    if List.is_empty tp then "" else "forall " ^ ty_params tp ^ ". "

  let qty_string f (qty : qty) =
    foralls qty.type_params ^ constraints f qty.constraints ^ f qty.ty

  let rec ty_debug ty =
    match ty with
    | TyBool -> "TyBool"
    | TyRecord (id, flds) ->
        Printf.sprintf "%s{%s}" id (ty_fields ty_debug flds)
    | TyVar { contents = Link ty } ->
        Printf.sprintf "TyVar(Link(%s))" (ty_debug ty)
    | TyVar { contents = Unbound (id, lvl) } ->
        Printf.sprintf "TyVar(Unbound(%s,%d))" id lvl
    | TyArrow arr ->
        "(" ^ String.concat ~sep:" -> " (List.map arr ~f:ty_debug) ^ ")"
    | TyName name -> name
    | TyApp app -> String.concat ~sep:" " (List.map app ~f:ty_debug)

  let tycon_debug = tycon_string ty_debug
  let qty_debug = qty_string ty_debug

  let rec ty_pretty ty =
    match force ty with
    | TyBool -> "bool"
    | TyRecord (id, flds) ->
        Printf.sprintf "%s{%s}" id (ty_fields ty_pretty flds)
    | TyVar { contents = Link _ } -> failwith "unexpected: Link"
    | TyVar { contents = Unbound (id, _) } -> id
    | TyArrow arr ->
        "(" ^ String.concat ~sep:" -> " (List.map arr ~f:ty_pretty) ^ ")"
    | TyName name -> name
    | TyApp app -> String.concat ~sep:" " (List.map app ~f:ty_pretty)

  let tycon_pretty = tycon_string ty_pretty
  let qty_pretty = qty_string ty_pretty

  (* The typechecker raises the following exceptions. *)
  exception Undefined of string
  exception Expected of string
  exception MissingField of string
  exception DuplicateDefinition of string
  exception UnificationFailure of string
  exception OccursCheck
  exception OverlappingInstance of string

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
      (Printf.sprintf "failed to unify type %s with %s" (ty_debug t1)
         (ty_debug t2))

  let overlapping_instance : id -> qty -> exn =
   fun trait_name qty ->
    let msg =
      if List.is_empty qty.type_params then
        Printf.sprintf "overlapping instance for %s %s" trait_name
          (ty_pretty qty.ty)
      else
        Printf.sprintf "overlapping instance for forall %s. %s %s"
          (ty_params qty.type_params)
          trait_name (ty_pretty qty.ty)
    in
    OverlappingInstance msg

  let expect_varbind bind =
    match bind with
    | VarBind ty -> ty
    | _ -> failwith "expected VarBind"

  let expect_unbound (tv : tv ref) =
    match !tv with
    | Unbound (id, lvl) -> (id, lvl)
    | _ -> failwith "expected Unbound"

  let expect_tyrecord ty =
    match ty with
    | TyRecord (id, flds) -> (id, flds)
    | _ -> raise (type_error "TyRecord" (ty_kind ty))

  (* Lookup a binding in the environment. *)
  let lookup (name : id) (e : env) : bind option = List.Assoc.find e ~equal name

  (* Lookup a variable's type in the environment. *)
  let lookup_var_type name (e : env) : qty =
    match lookup name e with
    | Some (VarBind t) -> t
    | _ -> raise (undefined_error "variable" name)

  (* Lookup a type constructor in the environment. *)
  let lookup_tycon name (e : env) : tycon =
    match lookup name e with
    | Some (TypeBind t) -> t
    | _ -> raise (undefined_error "type" name)

  (* Lookup a trait declaration in the environment. *)
  let lookup_trait name e : trait_decl =
    match lookup name e with
    | Some (TraitBind t) -> t
    | _ -> raise (undefined_error "trait" name)

  (* Get the type of a typed expression. *)
  let typ (texp : texp) : ty =
    match texp with
    | TEBool _ -> TyBool
    | TEVar (_, ty) -> ty
    | TEApp (_, _, ty) -> ty
    | TELam (_, _, ty) -> ty
    | TERecord (_, _, ty) -> ty
    | TEProj (_, _, ty) -> ty
    | TEIf (_, _, _, ty) -> ty
    | TELet (_, _, ty) -> ty
    | TELetRec (_, _, ty) -> ty

  (*= let add_instance impl ((trait_name, qty, _) as ins) =
    let l = Hashtbl.find_or_add impl.tbl trait_name ~default:(fun () -> []) in
    List.iter l ~f:(fun ty ->
        if overlap ty qty then raise (overlapping_instance ins));
    Hashtbl.set impl.tbl ~key:trait_name ~data:(qty :: l)

  let check_overlap trait_name impl_set ((ins_qty, _) as ins) : qty list =
    List.iter impl_set ~f:(fun qty ->
        if overlap qty ins_qty then raise (overlapping_instance trait_name ins));
    ins_qty :: impl_set *)

  (* ins.body *)
  (* unify ins.body's type with ins.qty. *)

  (* Zip over two lists, and apply a function to each pair of elements. If the
     lists have different lengths, stop at the shorter length. *)
  let[@tail_mod_cons] rec zipWith f l1 l2 =
    match (l1, l2) with
    | x :: xs, y :: ys -> f x y :: zipWith f xs ys
    | _ -> []

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

  let constraint_set : constraint_set = Hashtbl.create (module String)

  (* Create and initialize a hash table of ids and fresh unbound type
     variables. *)
  let create_table_for_type_params l =
    match
      Hashtbl.create_mapped
        (module String)
        ~get_key:Fn.id
        ~get_data:(fun _ -> fresh_unbound_var ())
        l
    with
    | `Ok tbl -> tbl
    | `Duplicate_keys _ -> failwith "unreachable: duplicate keys in type params"

  (* The environment stores quantified types, but sometimes, we need to
     associate a non-generalized type to a variable, e.g. the ELam and ELetRec
     rules. This function converts a type into a quantified type. *)
  let dont_generalize ty : qty = { type_params = []; constraints = []; ty }

  (* Generalize a type by constructing a quantified type containing type
     parameters corresponding to its unbound type variables. In order to decide
     whether to generalize an unbound type variable, we just check if its level
     is deeper than the current scope, i.e. the scope containing the let
     binding. *)
  let gen (ty : ty) : qty =
    let type_params = Hash_set.create (module String) in
    let rec gen' (ty : ty) : unit =
      match force ty with
      | TyVar { contents = Unbound (id, lvl) } when lvl > !current_level ->
          (* Generalize this unbound type variable only if its level is deeper
             than our current level. That is, it doesn't appear in the
             environment. *)
          Hash_set.add type_params id
      | TyArrow arr ->
          (* Generalize the type vars in the arrow type. *)
          List.iter arr ~f:gen'
      | TyApp app ->
          (* Generalize the type vars in the type application. *)
          List.iter app ~f:gen'
      | TyRecord (_, flds) ->
          (* Generalize the type vars in the record fields. *)
          List.iter ~f:(fun (_, ty) -> gen' ty) flds
      | _ -> ()
    in
    gen' ty;
    let type_params = Hash_set.to_list type_params |> List.sort ~compare in
    (* TODO: { type_params; ty } *)
    { type_params; constraints = []; ty }

  let print_constraints () =
    let f hs = String.concat ~sep:", " (Hash_set.to_list hs) in
    Hashtbl.iteri constraint_set ~f:(fun ~key ~data ->
        Stdio.printf "id: %s -> data: %s" key (f data))

  let find_cset cset tyvar_id =
    Hashtbl.find_or_add cset tyvar_id ~default:(fun () ->
        Hash_set.create (module String))

  let add_trait : constraint_set -> id -> id -> unit =
   fun cnt_set tyvar_id trait_name ->
    let set = find_cset cnt_set tyvar_id in
    Hash_set.add set trait_name

  let union_traits : constraint_set -> id -> id Hash_set.t -> unit =
   fun cset_dst tyvar_id cset_src ->
    (*= let tyvar_id =
      match ty with
      | TyVar { contents = Unbound (id, _) } -> id
      | _ -> failwith "TODO"
    in *)
    let set = find_cset cset_dst tyvar_id in
    Hash_set.iter cset_src ~f:(Hash_set.add set)

  let build_cset (env : env) (qty : qty) : constraint_set =
    ignore env;
    let cset = Hashtbl.create (module String) in
    List.iter qty.constraints ~f:(fun (trait_name, ty) ->
        match ty with
        | TyVar { contents = Unbound (tyvar_id, _) } ->
            add_trait cset tyvar_id trait_name
            (* also check if ty_name is in type_params *)
            (* if ty is more complicated, may want to simplify *)
        | TyName ty_name -> add_trait cset ty_name trait_name
        | _ -> failwith "unreachable");
    cset

  let rec find_instance (env : env) (trait_name : id) (ty : ty) =
    let td : trait_decl = lookup_trait trait_name env in
    (* look for instances in td.instances that match ty *)
    match List.find td.instances ~f:(fun ins -> true) with
    | Some (qty, _) ->
        qty
        (* build_cset env qty *)
        (* maybe this qty is then passed to propagate? or we build a cset from
           it? *)
        (* found the instance. if the instance has any predicates, we apply
           them. *)
    | None -> failwith "TODO: better error message for \"no such instance\""

  and propagate_ty (env : env) (trait_name : id) (ty : ty) : unit =
    let qty = find_instance env trait_name ty in
    unify env (inst env qty) ty
  (* () *)
  (* let cset = findInstanceContext env trait_name ty in *)
  (* List.iter cset *)
  (*= TODO:
       s = findInstanceContext env trait_name ty
       List.iter s.traitSet ~f:(fun trs -> List.iter (args ty) ~f:(fun ta -> propagateTraits env trs ta)) *)
  (* TODO *)

  and propagate_traits : env -> id Hash_set.t -> ty -> unit =
   fun env traits ty ->
    match ty with
    | TyVar { contents = Unbound (tyvar_id, _) } ->
        union_traits constraint_set tyvar_id traits
    | _ -> Hash_set.iter traits ~f:(fun c -> propagate_ty env c ty)

  and propagate : env -> constraint_set -> id -> ty -> unit =
   fun env cset id tv ->
    ignore env;
    match Hashtbl.find cset id with
    | Some traits ->
        (* findInstanceContext for tv *)
        propagate_traits env traits tv
    | None -> ()

  (* Instantiate a quantified type by replacing all the quantified type
     variables with fresh unbound type variables. Ensure that the same ID gets
     mapped to the same unbound type variable by using an (id, ty) Hashtbl. *)
  and inst ?tbl (env : env) (qty : qty) : ty =
    let tbl =
      (* If a hash table is provided, use it. Otherwise, create a new one. *)
      match tbl with
      | None -> create_table_for_type_params qty.type_params
      | Some tbl -> tbl
    in
    (* reverse index of (trait_name, ty) list, i.e. tyvar_id -> trait_name
       list *)
    let cset : constraint_set = build_cset env qty in
    (*= for each cnt in qty.constraints
          for ty_par_id in instanceLookupSimplify cnt
            ty = tbl[ty_par_id]
            for (trait_name, ty_var) instanceLookupSimplify ty
              constraint_st[ty_var] += trait_name *)
    let rec inst' (ty : ty) =
      match force ty with
      | TyVar { contents = Unbound (id, _) } as tv -> (
          (* If we see a quantified type variable, check if it's in the hash
             table. *)
          match Hashtbl.find tbl id with
          | Some tv ->
              propagate env cset id tv;
              tv (* If it is, return the type variable. *)
          | None -> tv)
      | TyName id as ty -> (
          (* In a type annotation, the quantified type variable will be referred
             to by a type name. *)
          match Hashtbl.find tbl id with
          | Some tv ->
              propagate env cset id tv;
              tv
          | None -> ty)
      | TyArrow arr ->
          (* Instantiate the type vars in the arrow type. *)
          TyArrow (List.map arr ~f:inst')
      | TyApp app ->
          (* Instantiate the type vars in the type application. *)
          TyApp (List.map app ~f:inst')
      | TyRecord (id, flds) ->
          (* Instantiate the type vars in the record fields. *)
          let inst_fld (id, ty) = (id, inst' ty) in
          TyRecord (id, List.map ~f:inst_fld flds)
      | ty -> ty
    in
    inst' qty.ty

  (* Perform a type application to get the underlying record type. We only need
     to apply the top-level, so that we can project and unify the record
     type. *)
  and apply_type env ty =
    match ty with
    | TyName id ->
        (* Nothing to apply, just look up the type constructor, and return its
           underlying type. *)
        let tc = lookup_tycon id env in
        TyRecord (tc.name, tc.ty)
    | TyApp (TyName id :: type_args) ->
        (* Look up the type constructor, and apply the type arguments for each
           of its type parameters. *)
        let tc = lookup_tycon id env in
        (* Hash table to keep track of type parameters we've applied. *)
        let tbl =
          (* Zip over type parameter names and the type arguments to build an
             association list that can be added to the hash table. *)
          match List.zip tc.type_params type_args with
          | Ok alist -> Hashtbl.of_alist_exn (module String) alist
          | Unequal_lengths ->
              failwith "incorrect number of arguments in type application"
        in
        (* Pass the table of applied type parameters into inst to substitute for
           the TyNames. *)
        inst env ~tbl
          (*{ type_params = []; ty = TyRecord (tc.name, tc.ty) } *)
          {
            type_params = tc.type_params;
            constraints = tc.constraints;
            ty = TyRecord (tc.name, tc.ty);
          }
    | _ -> failwith "expected TyName or TyApp"

  (* Occurs check: check if a type variable occurs in a type. If it does, raise
     an exception. Otherwise, update the type variable's level to be the minimum
     of its current level and the type's level. *)
  and occurs (src : tv ref) (ty : ty) : unit =
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
    | TyArrow arr ->
        (* Check that src occurs in the arrow type. *)
        List.iter arr ~f:(fun t -> occurs src t)
    | TyApp app ->
        (* Check that src occurs in the type application. *)
        List.iter app ~f:(fun t -> occurs src t)
    | TyRecord (_, flds) ->
        (* Check that src occurs in the field types. *)
        List.iter ~f:(fun (_, ty) -> occurs src ty) flds
    | _ -> ()

  (* Unify two types. If they are not unifiable, raise an exception. *)
  and unify (env : env) (t1 : ty) (t2 : ty) : unit =
    (* Follow all the links. If we see any type variables, they will only be
       Unbound. *)
    let t1, t2 = (force t1, force t2) in
    match (t1, t2) with
    | _ when equal t1 t2 ->
        () (* The types are trivially equal (e.g. TyBool). *)
    | TyVar tv, ty | ty, TyVar tv ->
        (* If either type is a type variable, ensure that the type variable does
           not occur in the type. Update the levels while you're at it. *)
        occurs tv ty;
        (* Link the type variable to the type. *)
        tv := Link ty
    | TyArrow arr1, TyArrow arr2 when List.length arr1 = List.length arr2 ->
        (* If both types are function types, unify their corresponding types
           with each other. *)
        List.iter2_exn arr1 arr2 ~f:(unify env)
    (* unify f1 f2; unify d1 d2 *)
    | TyRecord (id1, fds1), TyRecord (id2, fds2)
      when equal id1 id2 && equal (List.length fds1) (List.length fds2) ->
        (* Both types are records with the same name and number of fields. *)
        let unify_fld (id1, ty1) (id2, ty2) =
          if not (equal id1 id2) then raise (unify_failed ty1 ty2)
          else unify env ty1 ty2
        in
        (* Unify their corresponding fields. *)
        List.iter2_exn ~f:unify_fld fds1 fds2
    | TyApp app1, TyApp app2 when List.length app1 = List.length app2 ->
        (* If both types are type applications, unify their corresponding types
           with each other. *)
        List.iter2_exn app1 app2 ~f:(unify env)
    | TyName a, TyName b when equal a b -> () (* The type names are the same. *)
    | _ ->
        (* Unification has failed. *)
        raise (unify_failed t1 t2)

  let overlap (env : env) (a : qty) (b : qty) : bool =
    let ia = inst env a in
    let ib = inst env b in
    try
      unify env ia ib;
      true
    with UnificationFailure _ -> false

  (*= let rec overlap' (x : ty) (y : ty) : bool =
              match (x, y) with
              | _ when equal x y -> true
              | TyName id, _ when List.mem a.type_params id ~equal -> true
              | _, TyName id when List.mem b.type_params id ~equal -> true
              | TyName x, TyName y -> equal x y
              | TyApp app1, TyApp app2 -> List.for_all2_exn app1 app2 ~f:overlap'
              | TyArrow arr1, TyArrow arr2 -> List.for_all2_exn arr1 arr2 ~f:overlap'
              | _ -> false
            in
            overlap' a.ty b.ty *)
  let add_instance (env : env) trait_name ins_list (ins_qty, _) =
    List.iter ins_list ~f:(fun qty ->
        if overlap env qty ins_qty then
          raise (overlapping_instance trait_name ins_qty));
    ins_qty :: ins_list

  let inst_tycon tc =
    (* No type parameters, so all we need is the type name. *)
    if List.is_empty tc.type_params then TyName tc.name
    else
      (* Map over the type parameters to build up a TyApp with fresh unbound
         variables. *)
      TyApp
        (TyName tc.name
        :: List.map tc.type_params ~f:(fun _ -> fresh_unbound_var ()))

  let rec infer (env : env) (exp : exp) : texp =
    match exp with
    | EBool b -> TEBool (b, TyBool) (* A true/false value is of type Bool. *)
    | EVar name ->
        (* Variable is being used. Look up its type in the environment, *)
        let var_ty = lookup_var_type name env in
        (* Stdio.print_endline (qty_pretty var_ty); *)
        (* instantiate its type by replacing all of its quantified type
           variables with fresh unbound type variables.*)
        TEVar (name, inst env var_ty)
    | EApp (fn, arg) ->
        (* To typecheck a function application, first infer the types of the
           function and the argument. *)
        let fn = infer env fn in
        let arg = infer env arg in
        (* Instantiate a fresh type variable for the result of the application,
           and synthesize an arrow type going from the argument to the
           result. *)
        let ty_res = fresh_unbound_var () in
        let ty_arr = TyArrow [ typ arg; ty_res ] in
        (* Unify it with the function's type. *)
        unify env (typ fn) ty_arr;
        (* Return the result type. *)
        TEApp (fn, arg, ty_res)
    | ELam (param, body) ->
        (* Instantiate a fresh type variable for the lambda parameter, and
           extend the environment with the param and its type. *)
        let ty_param = fresh_unbound_var () in
        let env' = (param, VarBind (dont_generalize ty_param)) :: env in
        (* Typecheck the body of the lambda with the extended environment. *)
        let body = infer env' body in
        (* Return a synthesized arrow type from the parameter to the body. *)
        TELam (param, body, TyArrow [ ty_param; typ body ])
    | ERecord (tname, rec_lit) ->
        (* Look up the declared type constructor for the type name on the record
           literal. *)
        let tc = lookup_tycon tname env in
        (* Instantiate the type constructor into a type with fresh unbound
           variables. *)
        let ty_app = inst_tycon tc in
        (* Apply the type application to get a concrete record type that we can
           unify *)
        let ty_dec = apply_type env ty_app in
        (* Infer the types of all the fields in the literal. *)
        let rec_lit = List.map ~f:(fun (id, x) -> (id, infer env x)) rec_lit in
        (* Synthesize a record type with the types of those fields. *)
        let ty_rec =
          TyRecord (tname, List.map ~f:(fun (id, x) -> (id, typ x)) rec_lit)
        in
        (* Unify that with the declared type. *)
        unify env ty_dec ty_rec;
        (* Return the the type application representation. *)
        TERecord (tname, rec_lit, ty_app)
    | EProj (rcd, fld) -> (
        (* Infer the type of the expression we're projecting on. *)
        let rcd = infer env rcd in
        (* Concretize the type in case it's a type application. *)
        let ty_rcd = apply_type env (typ rcd) in
        (* Check that it's actually a record. *)
        let name, rec_ty = expect_tyrecord ty_rcd in
        (* Check that it has the field we're accessing. *)
        match List.Assoc.find rec_ty ~equal fld with
        (* Return the field's type in the record. *)
        | Some ty -> TEProj (rcd, fld, ty)
        | _ -> raise (missing_field fld name))
    | EIf (cond, thn, els) ->
        (* Check that the type of condition is Bool. *)
        let cond = infer env cond in
        unify env (typ cond) TyBool;
        (* Check that the types of the branches are equal to each other. *)
        let thn = infer env thn in
        let els = infer env els in
        unify env (typ thn) (typ els);
        (* Return the type of one of the branches. (we'll pick the "then"
           branch) *)
        TEIf (cond, thn, els, typ thn)
    | ELet ((id, ann, rhs), body) ->
        (* Increment the nesting level at this let binding. *)
        enter_level ();
        (* If there's a type annotation on this let binding, instantiate it. *)
        let ty_rhs =
          match ann with
          | Some ann -> inst env ann
          | None -> fresh_unbound_var ()
        in
        (* Infer the type of the right-hand-side. *)
        let rhs = infer env rhs in
        (* Unify it with the annotated type. *)
        unify env ty_rhs (typ rhs);
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
                | Some ann -> inst env ann
                | None -> fresh_unbound_var ()
              in
              (* Extend the environment by prepending the binding and its
                 type. *)
              (id, VarBind (dont_generalize ty_decl)) :: env'
        in
        let env' : env = List.fold_right ~f:extend_env ~init:env decls in
        (* Using the extended environment, infer the types of the
           right-hand-side of all the let declarations. *)
        let infer_let : id * bind -> let_decl -> tlet_decl =
         fun (id, bind) (_, ann, rhs) ->
          let ty_bind = expect_varbind bind in
          let rhs = infer env' rhs in
          unify env' ty_bind.ty (typ rhs);
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
  let checkTycon type_names trait_names tc =
    (* TODO: check that trait names that are referenced exist and are done in
       the appropriate places. *)
    let _ = trait_names in
    let names = Hash_set.copy type_names in
    List.iter tc.type_params ~f:(fun id -> Hash_set.add names id);
    let rec checkTycon' ty =
      match ty with
      | TyVar _ -> failwith "unexpected: TyVar"
      | TyArrow arr -> List.iter arr ~f:checkTycon'
      | TyApp (TyName _ :: _ as app) -> List.iter app ~f:checkTycon'
      | TyApp _ -> failwith "head of the type application should be a type name"
      | TyRecord (tname, flds) ->
          if not (Hash_set.mem names tname) then
            raise (undefined_error "type" tname);
          List.iter flds ~f:(fun (_, ty) -> checkTycon' ty)
      | TyName tname ->
          if not (Hash_set.mem names tname) then
            raise (undefined_error "type" tname)
      | TyBool -> ()
    in
    checkTycon' (TyRecord (tc.name, tc.ty))

  (* Should not mention trait name *)
  (*= let check_well_formed env (qty : qty) : unit =
    let type_params = Hash_set.of_list (module String) qty.type_params in
    let rec check_well_formed' (ty : ty) =
      match ty with
      | TyBool -> ()
      | TyRecord (_, _) -> failwith "should not exist"
      | TyVar _ -> failwith "should not exist"
      | TyArrow arr -> List.iter arr ~f:check_well_formed'
      | TyName name -> (match lookup name env with 
        | Some b ->
        | None -> if Hash_set.mem type_params name then () else 
      )
      | TyApp (TyName name :: tl)
        when List.length (lookup_tycon name env).type_params = List.length tl ->
          List.iter tl ~f:(check_well_formed env)
      | _ -> failwith "not well formed"
    in
    check_well_formed' qty.ty *)

  let prepend_defs (td : trait_decl) (env : env) =
    (* TODO: should this be a fold_right? doesn't really matter though *)
    List.fold_right td.def ~init:env ~f:(fun (id, ty) acc ->
        let qty : qty =
          {
            type_params = [ td.type_param ];
            constraints = [ (td.name, TyName td.type_param) ];
            ty;
          }
        in
        (id, VarBind qty) :: acc)

  (* Typecheck a program. *)
  let typecheck_prog : prog -> texp =
   fun { tycons = tcl; traits = trl; body = exp } ->
    let type_names = Hash_set.create (module String) in
    let trait_names = Hash_set.create (module String) in
    (* let impl : impl = { tbl = Hashtbl.create (module String) } in *)
    (* Do an initial pass over type declarations to check for duplicates and add
       their names to a Hash_set for checking their definitions. Also add these
       bindings to an environment that can be passed to infer. *)
    let env =
      List.fold_left tcl ~init:[] ~f:(fun acc tc ->
          (match Hash_set.strict_add type_names tc.name with
          | Ok () -> ()
          | Error _ -> raise (duplicate_definition tc.name));
          (tc.name, TypeBind tc) :: acc)
    in
    let env =
      (* Add trait methods to environment. *)
      List.fold_left trl ~init:env ~f:(fun acc td ->
          (* First, check if it collides with a type name. *)
          (if Hash_set.mem type_names td.name then
             raise (duplicate_definition td.name)
           else
             match Hash_set.strict_add trait_names td.name with
             | Ok () -> ()
             | Error _ -> raise (duplicate_definition td.name));
          ignore
            (List.fold_left td.instances ~init:[] ~f:(add_instance env td.name));
          (td.name, TraitBind td) :: prepend_defs td acc)
    in
    (* List.iter inl ~f:(fun ((trait_name, _, _) as ins) -> if not (Hash_set.mem
       trait_names trait_name) then raise (undefined_error "trait"
       trait_name) *)
    (* else check_well_formed env ins.qty; *)
    (* Do we really need to check well-formedness here if typechecking an
       instance declaration handles this?*)
    (* else add_instance impl ins); *)
    (* Walk tycons again to make sure that all type names and qvars are
       referenced. TODO: Is this necessary? *)
    List.iter tcl ~f:(checkTycon type_names trait_names);
    infer env exp
end

(* Tests *)

let assert_raises f e =
  try
    ignore (f ());
    false
  with exn -> (* Stdio.print_endline (Exn.to_string exn); *)
              equal exn e

let%test "1" =
  let open HM_SP () in
  let prog =
    {
      tycons =
        [
          {
            name = "box";
            type_params = [ "'a" ];
            constraints = [];
            ty = [ ("x", TyName "'a") ];
          };
        ];
      traits =
        [
          {
            name = "Eq";
            type_param = "'a";
            def = [];
            instances =
              [
                ({ type_params = []; constraints = []; ty = TyBool }, []);
                ( {
                    type_params = [ "'a" ];
                    constraints = [];
                    ty = TyApp [ TyName "box"; TyName "'a" ];
                  },
                  [] );
                ( { type_params = [ "'a" ]; constraints = []; ty = TyName "'a" },
                  [] );
              ];
          };
        ];
      body = EBool true;
    }
  in
  assert_raises
    (fun () -> typecheck_prog prog)
    (OverlappingInstance "overlapping instance for forall 'a. Eq 'a")

let%test "2" =
  let open HM_SP () in
  let prog =
    {
      tycons = [];
      traits =
        [
          {
            name = "Eq";
            type_param = "'a";
            def = [ ("eq", TyArrow [ TyName "'a"; TyName "'a"; TyBool ]) ];
            instances = [];
          };
        ];
      body = EVar "eq";
    }
  in
  let tprog = typecheck_prog prog in
  let t = typ tprog in
  (* pretty printer might need to look up constraints *)
  Stdio.print_endline (ty_pretty t);
  print_constraints ();
  true

(* try ignore (typecheck_prog prog); false with OverlappingInstance "overlapping
   instance for Eq forall 'a. box 'a" -> true *)
(* let _ = typ x in true *)
(*=
(* 1. let id = fun x -> x in id *)
let%test "1" =
  let open HM () in
  let prog = ([], ELet (("id", None, ELam ("x", EVar "x")), EVar "id")) in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "('2 -> '2)"

(* 2. fun x -> let y = fun z -> z in y *)
let%test "2" =
  let open HM () in
  let prog =
    ([], ELam ("x", ELet (("y", None, ELam ("z", EVar "z")), EVar "y")))
  in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "('0 -> ('3 -> '3))"

(* 3. fun x -> let y = x in y *)
let%test "3" =
  let open HM () in
  let prog = ([], ELam ("x", ELet (("y", None, EVar "x"), EVar "y"))) in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "('0 -> '0)"

(* 4. fun x -> let y = fun z -> x z in y *)
let%test "4" =
  let open HM () in
  let prog =
    ( [],
      ELam
        ( "x",
          ELet (("y", None, ELam ("z", EApp (EVar "x", EVar "z"))), EVar "y") )
    )
  in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "(('2 -> '3) -> ('2 -> '3))"

(* 5. if true then false else true *)
let%test "5" =
  let open HM () in
  let prog = ([], EIf (EBool true, EBool false, EBool true)) in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "bool"

(* 6. let f: 'a -> 'a = fun x -> x *)
let%test "6" =
  let open HM () in
  let prog =
    ( [],
      ELet
        ( ( "f",
            Some
              {
                type_params = [ "'a" ];
                ty = TyArrow [ TyName "'a"; TyName "'a" ];
              },
            ELam ("x", EVar "x") ),
          EApp (EVar "f", EBool true) ) )
  in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "bool"

(*= 7.
   type box 'a = { x: 'a }
   let r : box bool = box{x = true} in r *)
let%test "7" =
  let open HM () in
  let prog =
    ( [ { name = "box"; type_params = [ "'a" ]; ty = [ ("x", TyName "'a") ] } ],
      ELet
        ( ( "r",
            Some { type_params = []; ty = TyApp [ TyName "box"; TyBool ] },
            ERecord ("box", [ ("x", EBool true) ]) ),
          EVar "r" ) )
  in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "box bool"

(*= 8.
   type box 'a = { x: 'a }
   let r = box{x = true} in r.x
*)
let%test "8" =
  let open HM () in
  let prog =
    ( [ { name = "box"; type_params = [ "'a" ]; ty = [ ("x", TyName "'a") ] } ],
      ELet
        ( ( "r",
            Some { type_params = []; ty = TyApp [ TyName "box"; TyBool ] },
            ERecord ("box", [ ("x", EBool true) ]) ),
          EProj (EVar "r", "x") ) )
  in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "bool"

(*= 9.
   let rec f = fun x -> g x
   and g = fun x -> f x in f *)
let%test "9" =
  let open HM () in
  let prog =
    ( [],
      ELetRec
        ( [
            ("f", None, ELam ("x", EApp (EVar "g", EVar "x")));
            ("g", None, ELam ("x", EApp (EVar "f", EVar "x")));
          ],
          EVar "f" ) )
  in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "('6 -> '7)"

(* 10. let rec fix = fun f -> f (fix f) in fix *)
let%test "10" =
  let open HM () in
  let fix =
    ELetRec
      ( [
          ("fix", None, ELam ("f", EApp (EVar "f", EApp (EVar "fix", EVar "f"))));
        ],
        EVar "fix" )
  in
  let x = typecheck_prog ([], fix) in
  let t = typ x in
  Poly.equal (ty_pretty t) "(('4 -> '4) -> '4)"
*)
