open QCheck
open Effects

(** AST type definitions  *)

let reset_typevar, new_typevar =
  let count = ref 0 in
  ( (fun () -> count := 0)
  , fun () ->
      let old = !count in
      incr count ;
      old )


let reset_var, new_var =
  let count = ref 0 in
  ( (fun () -> count := 0)
  , fun () ->
      let old = !count in
      incr count ;
      "var" ^ string_of_int old )


type variable = string

type typevar = int

type etype =
  | Typevar of typevar
  | Unit
  | Int
  | Bool
  | String
  | Exn
  | List of etype
  | Fun of etype * effect * etype

let primitive_types = [ Unit; Int; Bool; String ]

let rec ftv = function
  | Typevar a ->
      [ a ]
  | Unit | Int | Bool | String | Exn ->
      []
  | List et ->
      ftv et
  | Fun (a, _, r) ->
      ftv a @ ftv r


let rec occurs tvar = function
  | Typevar a ->
      tvar = a
  | List a ->
      occurs tvar a
  | Fun (a, _, b) ->
      occurs tvar a || occurs tvar b
  | Unit | Int | Bool | String | Exn ->
      false


let rec arity = function
  | Fun (_, _, b) ->
      1 + arity b
  | Typevar _ | Unit | Int | Bool | String | List _ | Exn ->
      0


let rec subst repl t =
  match t with
  | Unit | Int | Bool | String | Exn ->
      t
  | Typevar a ->
    (try List.assoc a repl with Not_found -> t)
  | Fun (l, e, r) ->
      Fun (subst repl l, e, subst repl r)
  | List u ->
      List (subst repl u)


let rec normalize_latent_effs t =
  match t with
  | Typevar _ | Unit | Int | Bool | String | Exn ->
      t
  | List t' ->
      List (normalize_latent_effs t')
  | Fun (s, _, t) ->
      Fun (normalize_latent_effs s, Pure, normalize_latent_effs t)


let rec latent_effects t =
  match t with
  | Typevar _ | Unit | Int | Bool | String | Exn ->
      false
  | List t' ->
      latent_effects t'
  | Fun (s, e, t) ->
      if e = Pure then latent_effects s && latent_effects t else true


type unify_solution =
  | No_sol
  | Sol of (typevar * etype) list

exception No_solution

let effects_compat e e' = e = e'

let rec unify_list = function
  | [] ->
      []
  | (l, r) :: rest ->
      let sub = unify_list rest in
      ( match (subst sub l, subst sub r) with
      | Unit, Unit ->
          sub
      | Int, Int ->
          sub
      | Bool, Bool ->
          sub
      | String, String ->
          sub
      | Exn, Exn ->
          sub
      | Typevar a, Typevar b ->
          if a = b then sub else (a, r) :: sub
      | List a, List b ->
          unify_list [ (a, b) ] @ sub
      | Fun (a, e, b), Fun (c, e', d) when effects_compat e e' ->
          unify_list [ (a, c); (b, d) ] @ sub
      | Typevar a, _ when not (latent_effects r) ->
          if occurs a r then raise No_solution else (a, r) :: sub
      | _, Typevar a when not (latent_effects l) ->
          if occurs a l then raise No_solution else (a, l) :: sub
      | _, _ ->
          raise No_solution )


let unify r t = try Sol (unify_list [ (r, t) ]) with No_solution -> No_sol

(* determines whether the first arg is a generalization of the second *)
(* or framed differently: whether the second is a particular instance of the first *)
let rec types_compat t t' =
  match (t, t') with
  | Unit, Unit ->
      true
  | Int, Int ->
      true
  | Bool, Bool ->
      true
  | String, String ->
      true
  | Exn, Exn ->
      true
  | Fun (at, e, rt), Fun (at', e', rt') ->
      types_compat at' at && types_compat rt rt' && effects_compat e e'
  | List et, List et' ->
      types_compat et et'
  | Typevar _, _ when not (latent_effects t') ->
    (match unify t t' with No_sol -> false | Sol _ -> true)
  | _, Typevar _ ->
      false
  | _, _ ->
      false


let unified_types_compat t t' =
  match unify t t' with Sol sub -> types_compat (subst sub t) t' | No_sol -> false


type lit =
  | LitUnit
  | LitInt of int
  | LitBool of bool
  | LitStr of string
  | LitList of lit list

type term =
  | Lit of lit
  | Variable of etype * variable
  | Lambda of etype * variable * etype * term
  | App of etype * term * etype * term * effect
  | Let of variable * etype * term * term * etype * effect
  | If of etype * term * term * term * effect
  | Try of term * variable * term * etype * effect
  | Raise of term * etype * effect

(** Printing functions  *)

let rec type_to_ocaml ?(effannot = false) sb = function
  | Typevar a ->
      Buffer.add_string sb ("'a" ^ string_of_int a)
  | Unit ->
      Buffer.add_string sb "unit"
  | Int ->
      Buffer.add_string sb "int"
  | Bool ->
      Buffer.add_string sb "bool"
  | String ->
      Buffer.add_string sb "string"
  | Exn ->
      Buffer.add_string sb "exn"
  | List s ->
      Buffer.add_string sb "(" ;
      type_to_ocaml ~effannot sb s ;
      Buffer.add_string sb ") list"
  | Fun (s, e, t) ->
      ( match s with
      | Unit | Int | Bool | String | Exn ->
          type_to_ocaml ~effannot sb s
      | Fun (_, _, _) | Typevar _ | List _ ->
          Buffer.add_string sb "(" ;
          type_to_ocaml ~effannot sb s ;
          Buffer.add_string sb ")" ) ;
      if effannot
      then (
        Buffer.add_string sb " -" ;
        Buffer.add_string sb (eff_to_str e) ;
        Buffer.add_string sb "-> " )
      else Buffer.add_string sb " -> " ;
      type_to_ocaml ~effannot sb t


let rec lit_to_ocaml sb = function
  | LitUnit ->
      Buffer.add_string sb "()"
  | LitInt i ->
      if i < 0
      then (
        Buffer.add_string sb "(" ;
        Buffer.add_string sb (string_of_int i) ;
        Buffer.add_string sb ")" )
      else Buffer.add_string sb (string_of_int i)
  | LitBool b ->
      Buffer.add_string sb (string_of_bool b)
  | LitStr s ->
      Buffer.add_string sb "\"" ;
      Buffer.add_string sb s ;
      Buffer.add_string sb "\""
  | LitList ls ->
      Buffer.add_string sb "[" ;
      List.iter
        (fun l ->
          lit_to_ocaml sb l ;
          Buffer.add_string sb "; ")
        ls ;
      Buffer.add_string sb "]"


let type_to_str ?(effannot = false) typ =
  let sb = Buffer.create 20 in
  let () = type_to_ocaml ~effannot sb typ in
  Buffer.contents sb


let term_to_ocaml ?(typeannot = true) term =
  (* BNF grammar:

   exp ::= l | x | fun (x:t) -> exp | exp exp | let (x:t) = exp in exp

   Same language but unambiguously formulated grammar:

   exp ::= app | fun (x:t) -> exp | let (x:t) = exp in exp | if exp then exp else exp
   app ::= arg | app arg
   arg ::= l | x | (exp)

   The following prettyprinter is structured according to this grammar to cut down on
   the needless parentheses
*)
  let rec exp sb t =
    match t with
    | Lambda (_, x, t, m) ->
        Buffer.add_string sb "fun " ;
        if typeannot
        then (
          Buffer.add_string sb "(" ;
          Buffer.add_string sb x ;
          Buffer.add_string sb ":" ;
          type_to_ocaml sb t ;
          Buffer.add_string sb ")" )
        else Buffer.add_string sb x ;
        Buffer.add_string sb " -> " ;
        exp sb m
    | Let (x, t, m, n, _, _) ->
        Buffer.add_string sb "let " ;
        if typeannot
        then (
          Buffer.add_string sb "(" ;
          Buffer.add_string sb x ;
          Buffer.add_string sb ":" ;
          type_to_ocaml sb t ;
          Buffer.add_string sb ")" )
        else Buffer.add_string sb x ;
        Buffer.add_string sb " = " ;
        exp sb m ;
        Buffer.add_string sb " in " ;
        exp sb n
    | If (_, b, m, n, _) ->
        Buffer.add_string sb "if " ;
        exp sb b ;
        Buffer.add_string sb " then " ;
        exp sb m ;
        Buffer.add_string sb " else " ;
        exp sb n
    | Try (e1, x, e2, _, _) ->
        Buffer.add_string sb "try " ;
        exp sb e1 ;
        Buffer.add_string sb " with " ;
        Buffer.add_string sb x ;
        Buffer.add_string sb " -> " ;
        exp sb e2
    | Raise (e, _, _) ->
        Buffer.add_string sb "raise (" ;
        exp sb e ;
        Buffer.add_string sb ")"
    | _ ->
        app sb t
  and app sb t =
    match t with
    | App (_, m, _, n, _) ->
        app sb m ;
        Buffer.add_string sb " " ;
        arg sb n
    | _ ->
        arg sb t
  and arg sb t =
    match t with
    | Lit l ->
        lit_to_ocaml sb l
    | Variable (_, s) ->
        Buffer.add_string sb s
    | _ ->
        Buffer.add_string sb "(" ;
        exp sb t ;
        Buffer.add_string sb ")"
  in
  let sb = Buffer.create 80 in
  let () = exp sb term in
  Buffer.contents sb


let lit_to_str lit =
  let sb = Buffer.create 20 in
  let () = lit_to_ocaml sb lit in
  Buffer.contents sb


let lit_message function_name l1 l2 message =
  function_name ^ ": " ^ lit_to_str l1 ^ " = " ^ lit_to_str l2 ^ " ? (" ^ message ^ ")"


let type_message function_name t1 t2 message =
  function_name
  ^ " : ("
  ^ type_to_str ~effannot:true t1
  ^ ") = ("
  ^ type_to_str ~effannot:true t2
  ^ ") ? Message : "
  ^ message


let effect_message function_name effect1 effect2 message =
  function_name
  ^ " : "
  ^ eff_to_str effect1
  ^ " = "
  ^ eff_to_str effect2
  ^ " ? Message : "
  ^ message


let imm_eff t =
  match t with
  | Lit _ | Variable (_, _) | Lambda (_, _, _, _) ->
      Pure
  | App (_, _, _, _, e) ->
      e
  | Let (_, _, _, _, _, e) ->
      e
  | If (_, _, _, _, e) ->
      e
  | Try (_, _, _, _, e) ->
      e
  | Raise (_, _, e) ->
      e


let imm_type t =
  let rec lit_type l =
    match l with
    | LitUnit ->
        Unit
    | LitInt _ ->
        Int
    | LitBool _ ->
        Bool
    | LitStr _ ->
        String
    | LitList l ->
        let etyp =
          List.fold_left
            (fun typacc elem ->
              let etyp = lit_type elem in
              if types_compat typacc etyp (* if typacc is a generalization of etyp *)
              then etyp
              else if types_compat etyp typacc
                      (* if etyp is a generalization of typeacc *)
              then typacc
              else
                failwith
                  ( "lit_type: elements in list literal disagree"
                  ^ "  typacc is "
                  ^ type_to_str ~effannot:true typacc
                  ^ "  etyp is "
                  ^ type_to_str ~effannot:true etyp ))
            (Typevar (new_typevar ()))
            l
        in
        List etyp
  in
  match t with
  | Lit l ->
      lit_type l
  | Variable (typ, _) ->
      typ
  | Lambda (typ, _, _, _) ->
      typ
  | App (typ, _, _, _, _) ->
      typ
  | Let (_, _, _, _, typ, _) ->
      typ
  | If (typ, _, _, _, _) ->
      typ
  | Try (_, _, _, typ, _) ->
      typ
  | Raise (_, typ, _) ->
      typ


let rec return_types = function
  | Fun (s, e, t) ->
      Fun (s, e, t) :: return_types t
  | t ->
      [ t ]


(* determines whether x occurs free (outside a binding) in the arg. exp *)
let rec fv x = function
  | Lit _ ->
      false
  | Variable (_, y) ->
      x = y
  | Lambda (_, y, _, m) ->
      if x = y then false else fv x m
  | App (_, m, _, n, _) ->
      fv x m || fv x n
  | Let (y, _, m, n, _, _) ->
      fv x m || if x = y then false else fv x n
  | If (_, b, m, n, _) ->
      fv x b || fv x m || fv x n
  | Try (m, y, n, _, _) ->
      fv x m || if x = y then false else fv x n
  | Raise (m, _, _) ->
      fv x m


(* renames free occurrences of 'x' into 'y' *)
let rec alpha_rename m x y =
  match m with
  | Lit _ ->
      m
  | Variable (t, z) ->
      if x = z then Variable (t, y) else m
  | Lambda (t, z, t', m') ->
      if x = z then m else Lambda (t, z, t', alpha_rename m' x y)
  | App (rt, m, at, n, e) ->
      App (rt, alpha_rename m x y, at, alpha_rename n x y, e)
  | Let (z, t, m, n, t', e) ->
      let m' = alpha_rename m x y in
      let n' = if x = z then n else alpha_rename n x y in
      Let (z, t, m', n', t', e)
  | If (t, b, n, n', e) ->
      If (t, alpha_rename b x y, alpha_rename n x y, alpha_rename n' x y, e)
  | Try (m, z, n, typ, effect) ->
      let m' = alpha_rename m x y in
      let n' = if x = z then n else alpha_rename n x y in
      Try (m', z, n', typ, effect)
  | Raise (m, typ, effect) ->
      Raise (alpha_rename m x y, typ, effect)


let unify_and_subst t1 t2 =
  match unify t1 t2 with
  | Sol sub ->
      let t = subst sub t1 in
      if types_compat t1 t
      then
        if types_compat t2 t
        then t
        else failwith (type_message "unify_and_subst" t2 t "t2")
      else failwith (type_message "unify_and_subst" t1 t "t1")
  | No_sol ->
      failwith (type_message "unify_and_subst" t1 t2 "t1 cannot unify with t2")


let rec literal_to_ast sb = function
  | LitUnit ->
      Buffer.add_string sb "LitUnit"
  | LitInt n ->
      Buffer.add_string sb "LitInt " ;
      Buffer.add_string sb (string_of_int n)
  | LitBool b ->
      Buffer.add_string sb "LitBool " ;
      Buffer.add_string sb (string_of_bool b)
  | LitStr str ->
      Buffer.add_string sb "LitStr \"" ;
      Buffer.add_string sb str ;
      Buffer.add_string sb "\""
  | LitList litList ->
      Buffer.add_string sb "LitList [" ;
      List.iter
        (fun lit ->
          literal_to_ast sb lit ;
          Buffer.add_string sb "; ")
        litList ;
      Buffer.add_string sb "]"


let rec effect_to_ast sb = function
  | Pure ->
      Buffer.add_string sb "Pure"
  | Output ->
      Buffer.add_string sb "Output"
  | Mixed ->
      Buffer.add_string sb "Mixed"
  | Eval ->
      Buffer.add_string sb "Eval"
  | Exception ->
      Buffer.add_string sb "Exception"


let rec type_to_ast sb = function
  | Typevar a ->
      Buffer.add_string sb "Typevar " ;
      Buffer.add_string sb (string_of_int a)
  | Unit ->
      Buffer.add_string sb "Unit"
  | Int ->
      Buffer.add_string sb "Int"
  | Bool ->
      Buffer.add_string sb "Bool"
  | String ->
      Buffer.add_string sb "String"
  | Exn ->
      Buffer.add_string sb "Exn"
  | List s ->
      Buffer.add_string sb "List (" ;
      type_to_ast sb s ;
      Buffer.add_string sb ")"
  | Fun (s, e, t) ->
      Buffer.add_string sb "Fun (" ;
      type_to_ast sb s ;
      Buffer.add_string sb ", " ;
      effect_to_ast sb e ;
      Buffer.add_string sb ", " ;
      type_to_ast sb t ;
      Buffer.add_string sb ")"


let term_to_ast term =
  let rec term_to_ast' sb t =
    match t with
    | Lambda (t1, x, t2, m) ->
        Buffer.add_string sb "Lambda (" ;
        type_to_ast sb t1 ;
        Buffer.add_string sb ", \"" ;
        Buffer.add_string sb x ;
        Buffer.add_string sb "\", " ;
        type_to_ast sb t2 ;
        Buffer.add_string sb ", " ;
        term_to_ast' sb m ;
        Buffer.add_string sb ")"
    | Let (x, t1, m, n, t2, effect) ->
        Buffer.add_string sb "Let (\"" ;
        Buffer.add_string sb x ;
        Buffer.add_string sb "\", " ;
        type_to_ast sb t1 ;
        Buffer.add_string sb ", " ;
        term_to_ast' sb m ;
        Buffer.add_string sb ", " ;
        term_to_ast' sb n ;
        Buffer.add_string sb ", " ;
        type_to_ast sb t2 ;
        Buffer.add_string sb ", " ;
        effect_to_ast sb effect ;
        Buffer.add_string sb ")"
    | If (t, b, m, n, effect) ->
        Buffer.add_string sb "If (" ;
        type_to_ast sb t ;
        Buffer.add_string sb ", " ;
        term_to_ast' sb b ;
        Buffer.add_string sb ", " ;
        term_to_ast' sb m ;
        Buffer.add_string sb ", " ;
        term_to_ast' sb n ;
        Buffer.add_string sb ", " ;
        effect_to_ast sb effect ;
        Buffer.add_string sb ")"
    | Try (e1, x, e2, t, effect) ->
        Buffer.add_string sb "Try (" ;
        term_to_ast' sb e1 ;
        Buffer.add_string sb ", \"" ;
        Buffer.add_string sb x ;
        Buffer.add_string sb "\", " ;
        term_to_ast' sb e2 ;
        Buffer.add_string sb ", " ;
        type_to_ast sb t ;
        Buffer.add_string sb ", " ;
        effect_to_ast sb effect ;
        Buffer.add_string sb ")"
    | Raise (m, _type, effect) ->
        Buffer.add_string sb "Raise (" ;
        term_to_ast' sb m ;
        Buffer.add_string sb ", " ;
        type_to_ast sb _type ;
        Buffer.add_string sb ", " ;
        effect_to_ast sb effect ;
        Buffer.add_string sb ")"
    | App (t1, m, t2, n, effect) ->
        Buffer.add_string sb "App (" ;
        type_to_ast sb t1 ;
        Buffer.add_string sb ", " ;
        term_to_ast' sb m ;
        Buffer.add_string sb ", " ;
        type_to_ast sb t2 ;
        Buffer.add_string sb ", " ;
        term_to_ast' sb n ;
        Buffer.add_string sb ", " ;
        effect_to_ast sb effect ;
        Buffer.add_string sb ")"
    | Lit l ->
        Buffer.add_string sb "Lit (" ;
        literal_to_ast sb l ;
        Buffer.add_string sb ")"
    | Variable (t, s) ->
        Buffer.add_string sb "Variable (" ;
        type_to_ast sb t ;
        Buffer.add_string sb ", \"" ;
        Buffer.add_string sb s ;
        Buffer.add_string sb "\")"
  in
  let sb = Buffer.create 300 in
  let () = term_to_ast' sb term in
  Buffer.contents sb
