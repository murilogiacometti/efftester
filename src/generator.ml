open QCheck
open Ast
open Effects
open Env
open Tcheck

let effects_to_generate = [ Output; Pure; Mixed; Exception ]

let cartesian2 l = List.concat (List.map (fun e -> List.map (fun e' -> (e, e')) l) l)

let cartesian3 l =
  List.concat
    (List.concat
       (List.map (fun e -> List.map (fun e' -> List.map (fun e'' -> (e, e', e'')) l) l) l))


let reverse_1 f effect = List.filter (fun eff -> f eff = effect) effects_to_generate

let reverse_2 f effect =
  List.filter (fun (eff1, eff2) -> f eff1 eff2 = effect) (cartesian2 effects_to_generate)


let reverse_3 f effect =
  List.filter
    (fun (eff1, eff2, eff3) -> f eff1 eff2 eff3 = effect)
    (cartesian3 effects_to_generate)


(** Generators *)

let gen_reverse_effect_1 f effect =
  let reverse_list = reverse_1 f effect in
  Gen.oneofl reverse_list


let gen_reverse_effect_2 f effect = Gen.oneofl (reverse_2 f effect)

let gen_reverse_effect_3 f effect = Gen.oneofl (reverse_3 f effect)

let alpha_gen = Gen.map char_of_int (Gen.int_range (int_of_char 'a') (int_of_char 'z'))

let var_gen = Gen.map (String.make 1) alpha_gen

let string_gen = Gen.small_string ~gen:alpha_gen

let string_to_string s = "\"" ^ s ^ "\""

let sqrt i = int_of_float (sqrt (float_of_int i))

let arb_int =
  frequency [ (10, small_int); (5, int); (1, oneofl [ min_int; -1; 0; 1; max_int ]) ]


let int_gen = arb_int.gen

let if_type_generator ~expected_type ~expected_effect _then = function
  | None ->
      Gen.return None
  | Some term ->
      let _type, effect = (imm_type term, imm_eff term) in
      if unified_types_compat _type expected_type && types_compat _type expected_type
      then if effects_compat effect expected_effect then _then term else Gen.return None
      else Gen.return None


(* Type-directed literal generator *)
let rec literal_gen t eff size =
  match t with
  | Unit ->
      Gen.return LitUnit
  | Int ->
      Gen.map (fun i -> LitInt i) int_gen
  | Bool ->
      Gen.map (fun b -> LitBool b) Gen.bool
  | String ->
      Gen.map (fun s -> LitStr s) string_gen
  | List (Typevar _) ->
      Gen.return (LitList [])
  | List t ->
      if size = 0
      then Gen.return (LitList [])
      else
        Gen.map
          (fun ls -> LitList ls)
          (Gen.list_size (Gen.int_bound (sqrt size)) (literal_gen t eff (sqrt size)))
  (*     (Gen.list_size (Gen.int_bound (size/2)) (literal_gen t eff (size/2))) *)
  (* FIXME: - one element should/can have effect, if 'eff' allows *)
  (*        - list items should be able to contain arbitrary effectful exps *)
  | Typevar _ ->
      failwith "literal_gen: typevar arg. should not happen"
  | Fun _ ->
      failwith "literal_gen: funtype arg. should not happen"
  | Exn ->
      failwith "literal_gen: exntype arg. should not happen"


let create_lit t =
  let to_term s = Some (Lit s) in
  match t with
  | Unit ->
      to_term LitUnit
  | Int ->
      to_term (LitInt (Gen.generate1 small_int.gen))
  | Bool ->
      to_term (LitBool (Gen.generate1 bool.gen))
  | String ->
      to_term (LitStr (Gen.generate1 string_gen))
  | List _ | Fun _ | Typevar _ | Exn ->
      None


let eff_gen = Gen.oneofl [ Pure; Output ]

(* Generates ground types (without type variables) *)
let type_gen =
  Gen.fix (fun recgen n ->
      if n = 0
      then Gen.oneofl primitive_types
      else
        Gen.frequency
          [ (* Generate no alphas *)
            (4, Gen.oneofl primitive_types)
          ; (1, Gen.map (fun t -> List t) (recgen (n / 2)))
          ; ( 1
            , Gen.map3
                (fun t e t' -> Fun (t, e, t'))
                (recgen (n / 2))
                eff_gen
                (recgen (n / 2)) )
          ])


let rec list_of_non_literal = function
  | List s ->
      list_of_non_literal s
  | Fun _ ->
      true
  | Exn ->
      true
  | _ ->
      false


(* Sized generator of variables according to the LIT rule 
   @param env  : surrounding environment
   @param s    : desired goal type
   @param eff  : desired effect
   @param size : size parameter

   --------------------- (LIT)
       env |- l : s
*)
let lit_rules _ s eff size =
  if eff = Pure
  then
    match s with
    | List s when list_of_non_literal s ->
        []
    | Unit | Int | Bool | String | List _ ->
        [ (6, Gen.map (fun l -> Some (Lit l)) (literal_gen s eff size)) ]
    | Fun _ | Typevar _ | Exn ->
        []
  else []


(* Sized generator of variables according to the VAR rule 
   @param env  : surrounding environment
   @param s    : desired goal type
   @param eff  : desired effect
   @param size : size parameter

      (t:s) \in env
   --------------------- (VAR)
       env |- t : s
*)
let var_rules env s eff _ =
  let candvars = VarSet.elements (lookup_type s env) in
  let candvars' =
    List.filter
      (fun x ->
        match lookup_var x env with
        | Some t ->
            arity t = arity s && types_compat t s
        | None ->
            failwith ("var_rules: found variable " ^ x ^ " without associated type"))
      candvars
  in
  if eff = Pure
  then List.map (fun var -> (1, Gen.return (Some (Variable (s, var))))) candvars'
  else []


(* Sized generator of lambda terms according to the LAM rule 
   @param env  : surrounding environment
   @param u    : desired goal type
   @param eff  : desired effect
   @param size : size parameter

               (x:s), env |- m : t
    -------------------------------------------- (LAM)
       env |- (fun (x:s) -> m) : s -> t
*)
let rec lam_rules env u eff size =
  let gen s eff t =
    Gen.(
      var_gen
      >>= fun x ->
      list_permute_term_gen_outer (add_var x s env) t eff (size / 2)
      >>= if_type_generator ~expected_type:t ~expected_effect:eff (fun m ->
              let myeff = imm_eff m in
              if effects_compat myeff eff
              then return (Some (Lambda (Fun (s, myeff, imm_type m), x, s, m)))
              else return None))
  in
  if eff = Pure
  then
    match u with
    | Unit | Int | Bool | String | List _ | Typevar _ | Exn ->
        []
    | Fun (s, e, t) ->
        [ (8, gen s e t) ]
  else []


(* Sized generator of applications (calls) according to the APP rule 
   @param env  : surrounding environment
   @param t    : desired goal type
   @param eff  : desired effect
   @param size : size parameter

       env |- f : s -> t     env |- x : s
    ---------------------------------------- (APP)
                 env |- f x : t
*)
and app_rules env t eff size =
  let open Gen in
  let first_or_second_pure ~first_pure s =
    let reverse_function =
      if first_pure
      then fun latent_effect second -> eff_app latent_effect Pure second
      else fun latent_effect first -> eff_app latent_effect first Pure
    in
    gen_reverse_effect_2 reverse_function eff
    >>= fun (latent_effect, first_or_second_effect) ->
    let first_effect, second_effect =
      if first_pure
      then (Pure, first_or_second_effect)
      else (first_or_second_effect, Pure)
    in
    list_permute_term_gen_outer env (Fun (s, latent_effect, t)) first_effect (size / 2)
    >>= if_type_generator
          ~expected_type:(Fun (s, latent_effect, t))
          ~expected_effect:first_effect
          (fun f ->
            list_permute_term_gen_outer env s second_effect (size / 2)
            >>= if_type_generator
                  ~expected_type:s
                  ~expected_effect:second_effect
                  (fun x ->
                    match imm_type f with
                    | Fun (_, latent_eff, frange) ->
                        let funeff = imm_eff f in
                        let argeff = imm_eff x in
                        let eff' = eff_app latent_eff funeff argeff in
                        if types_compat frange t
                        then
                          if effects_compat eff' eff
                          then Gen.return (Some (App (frange, f, imm_type x, x, eff')))
                          else Gen.return None
                        else Gen.return None
                    | Typevar _ ->
                        let funeff = imm_eff f in
                        let argeff = imm_eff x in
                        let eff' = eff_app Pure funeff argeff in
                        if types_compat (imm_type f) t
                        then
                          if effects_compat eff' eff
                             && latent_effect = Pure
                             && not (latent_effects t)
                          then
                            Gen.return
                              (Some
                                 (App (Typevar (new_typevar ()), f, imm_type x, x, eff')))
                          else Gen.return None
                        else Gen.return None
                    | _ ->
                        failwith
                          ( "app_rules generated application with non-function  "
                          ^ " t is "
                          ^ type_to_str ~effannot:true t
                          ^ " f is "
                          ^ term_to_ocaml ~typeannot:false f
                          ^ " imm_type f is "
                          ^ type_to_str ~effannot:true (imm_type f) )))
  in
  (* May generate eff in either operator or operand *)
  [ (4, type_gen (size / 2) >>= first_or_second_pure ~first_pure:true)
  ; (4, type_gen (size / 2) >>= first_or_second_pure ~first_pure:false)
  ]


(* Sized generator of let according to the LET rule 
   @param env  : surrounding environment
   @param t    : desired goal type
   @param eff  : desired effect
   @param size : size parameter

       env |- m : s     env, (x:s) |- n : t
    ------------------------------------------ (LET)
           env |- let x:s = m in n : t
*)
and let_rules env t eff size =
  let open Gen in
  let from_type s =
    (* Generate two effects whose combination with 'eff_try' gives 'eff' *)
    gen_reverse_effect_2 eff_let eff
    >>= fun (m_effect_expected, n_effect_expected) ->
    var_gen
    >>= fun x ->
    list_permute_term_gen_outer env s m_effect_expected (size / 2)
    >>= if_type_generator ~expected_type:s ~expected_effect:m_effect_expected (fun m ->
            list_permute_term_gen_outer
              (add_var x (imm_type m) env)
              t
              n_effect_expected
              (size / 2)
            >>= if_type_generator
                  ~expected_type:t
                  ~expected_effect:n_effect_expected
                  (fun n ->
                    let myeff = eff_let (imm_eff m) (imm_eff n) in
                    if effects_compat myeff eff
                    then return (Some (Let (x, imm_type m, m, n, imm_type n, myeff)))
                    else return None))
  in
  [ (6, type_gen (size / 2) >>= from_type) ]


and try_rules env t eff size =
  let open Gen in
  let gen =
    (* Generate two effects whose combination with 'eff_try' gives 'eff' *)
    gen_reverse_effect_2 eff_try eff
    >>= fun (e1_effect_expected, e2_effect_expected) ->
    var_gen
    >>= fun x ->
    list_permute_term_gen_outer env t e1_effect_expected (size / 2)
    >>= if_type_generator ~expected_type:t ~expected_effect:e1_effect_expected (fun e1 ->
            let e1_type = imm_type e1 in
            let e1_effect = imm_eff e1 in
            let e2_type_expected = unify_and_subst e1_type t in
            list_permute_term_gen_outer
              (add_var x Exn env)
              e2_type_expected
              e2_effect_expected
              (size / 2)
            >>= if_type_generator
                  ~expected_type:e2_type_expected
                  ~expected_effect:e2_effect_expected
                  (fun e2 ->
                    let e2_type = imm_type e2 in
                    let e2_effect = imm_eff e2 in
                    let myeff = eff_try e1_effect e2_effect in
                    let mytype = unify_and_subst e1_type e2_type in
                    if effects_compat myeff eff
                    then return (Some (Try (e1, x, e2, mytype, myeff)))
                    else return None))
  in
  [ (6, gen) ]


and raise_rules env t eff size =
  let open Gen in
  let gen =
    match reverse_1 eff_raise eff with
    | [] ->
        return None
    | _ ->
        gen_reverse_effect_1 eff_raise eff
        >>= fun e_effect_expected ->
        list_permute_term_gen_outer env Exn e_effect_expected (size / 2)
        >>= if_type_generator
              ~expected_type:Exn
              ~expected_effect:e_effect_expected
              (fun e ->
                let exception_effect = imm_eff e in
                let raise_effect = eff_raise exception_effect in
                if effects_compat raise_effect eff
                then return (Some (Raise (e, Typevar (new_typevar ()), raise_effect)))
                else return None)
  in
  if latent_effects t
  then failwith "Latent effect expected in generated type"
  else [ (3, gen) ]


and if_rules env t eff size =
  let open Gen in
  let gen =
    (* Generate three effects whose combination with 'eff_if' gives 'eff' *)
    gen_reverse_effect_3 eff_if eff
    >>= fun (b_effect_expected, then_effect_expected, else_effect_expected) ->
    list_permute_term_gen_outer env Bool b_effect_expected (size / 3)
    >>= if_type_generator
          ~expected_type:Bool
          ~expected_effect:b_effect_expected
          (fun b ->
            list_permute_term_gen_outer env t then_effect_expected (size / 3)
            >>= if_type_generator
                  ~expected_type:t
                  ~expected_effect:then_effect_expected
                  (fun m ->
                    let then_type = imm_type m in
                    let then_effect = imm_eff m in
                    let subst_t = unify_and_subst then_type t in
                    list_permute_term_gen_outer
                      env
                      subst_t
                      else_effect_expected
                      (size / 3)
                    >>= if_type_generator
                          ~expected_type:subst_t
                          ~expected_effect:else_effect_expected
                          (fun n ->
                            let else_type = imm_type n in
                            let else_effect = imm_eff n in
                            let mytype = unify_and_subst then_type else_type in
                            let myeff = eff_if (imm_eff b) then_effect else_effect in
                            return (Some (If (mytype, b, m, n, myeff))))))
  in
  [ (3, gen) ]


and list_permute_term_gen_inner env goal size rules =
  let rec remove_at n xs =
    match (n, xs) with
    | 0, _ :: xs ->
        xs
    | n, x :: xs ->
        x :: remove_at (n - 1) xs
    | _ ->
        failwith "index out of bounds"
  in
  let elements_weighted xs =
    let _, ig =
      List.fold_left
        (fun (i, acc) (w, g) -> (i + 1, (w, Gen.pair (Gen.return i) g) :: acc))
        (0, [])
        xs
    in
    Gen.frequency ig
  in
  let to_term i = function
    | Some term ->
        Gen.return (Some term)
    | None ->
        let remainingRules = remove_at i rules in
        list_permute_term_gen_inner env goal size remainingRules
  in
  if rules = []
  then Gen.return None
  else Gen.(elements_weighted rules >>= fun (i, t) -> to_term i t)


and list_permute_term_gen_outer env goal eff size =
  (* indir_rule needs to be re-implemented to guarantee desired type *)
  let rules =
    List.concat
      ( (if eff = Pure then [ lit_rules env goal eff size ] else [])
      @ (if eff = Pure then [ var_rules env goal eff size ] else [])
      @ (if eff = Pure then [ lam_rules env goal eff size ] else [])
      @ (if size > 0 then [ app_rules env goal eff size ] else [])
      @ (if size > 0 then [ let_rules env goal eff size ] else [])
      @ (if size > 0 then [ try_rules env goal eff size ] else [])
      (*@ (if size > 0 then [ if_rules env goal eff size ] else [])*)
      @
      if size > 0 && (not (latent_effects goal)) && (eff = Mixed || eff = Exception)
      then [ raise_rules env goal eff size ]
      else [] )
  in
  list_permute_term_gen_inner env goal size rules


let list_permute_term_gen_rec_wrapper env goal eff =
  Gen.sized_size (Gen.int_range 1 300) (list_permute_term_gen_outer env goal eff)


(** Initial environment *)

let init_tri_env =
  List.fold_left
    (fun acc (var, t) -> add_var var t acc)
    (VarMap.empty, TypeMap.empty, TypeMap.empty)
    [ (* These follow the order and specification of the Pervasives module
         	  https://caml.inria.fr/pub/docs/manual-ocaml/libref/Pervasives.html *)
      (* Exceptions *)
      ("Not_found", Exn) (* Comparisons *)
    ; ( "(=)"
      , let a = Typevar (new_typevar ()) in
        Fun (a, Pure, Fun (a, Mixed, Bool)) )
    ; ( "(<>)"
      , let a = Typevar (new_typevar ()) in
        Fun (a, Pure, Fun (a, Mixed, Bool)) )
    ; ("(<)", Fun (Int, Pure, Fun (Int, Mixed, Bool)))
    ; ("(>)", Fun (Int, Pure, Fun (Int, Mixed, Bool)))
    ; (*   ("(<=)",           let a = Typevar (new_typevar()) in
               			Fun (a, Pure, Fun (a, (true,false), Bool)));
               ("(>=)",           let a = Typevar (new_typevar()) in
               			Fun (a, Pure, Fun (a, (true,false), Bool))); *)
      ( "compare"
      , let a = Typevar (new_typevar ()) in
        Fun (a, Pure, Fun (a, Mixed, Int)) )
    ; (*   ("min",            let a = Typevar (new_typevar()) in
               			Fun (a, Pure, Fun (a, (true,false), a)));
               ("max",            let a = Typevar (new_typevar()) in
               			Fun (a, Pure, Fun (a, (true,false), a)));
               ("(==)",           let a = Typevar (new_typevar()) in
               			Fun (a, Pure, Fun (a, (true,false), Bool)));
               ("(!=)",           let a = Typevar (new_typevar()) in
               			Fun (a, Pure, Fun (a, (true,false), Bool))); *)
      (* Boolean operations *)
      ("not", Fun (Bool, Pure, Bool))
    ; ("(&&)", Fun (Bool, Pure, Fun (Bool, Pure, Bool)))
    ; ("(||)", Fun (Bool, Pure, Fun (Bool, Pure, Bool)))
    ; (* Integer arithmetic *)
      (*   ("(~-)",           Fun (Int, Pure, Int));
           ("(~+)",           Fun (Int, Pure, Int)); *)
      ("succ", Fun (Int, Pure, Int))
    ; ("pred", Fun (Int, Pure, Int))
    ; ("(+)", Fun (Int, Pure, Fun (Int, Pure, Int)))
    ; ("(-)", Fun (Int, Pure, Fun (Int, Pure, Int)))
    ; ("( * )", Fun (Int, Pure, Fun (Int, Pure, Int)))
    ; ("(/)", Fun (Int, Pure, Fun (Int, Mixed, Int)))
    ; ("(mod)", Fun (Int, Pure, Fun (Int, Mixed, Int)))
    ; ("abs", Fun (Int, Pure, Int))
    ; (*   ("max_int",        Int);
               ("min_int",        Int); *)
      (* Bitwise operations *)
      ("(land)", Fun (Int, Pure, Fun (Int, Pure, Int)))
    ; ("(lor)", Fun (Int, Pure, Fun (Int, Pure, Int)))
    ; ("(lxor)", Fun (Int, Pure, Fun (Int, Pure, Int)))
    ; ("lnot", Fun (Int, Pure, Int))
    ; ("(lsl)", Fun (Int, Pure, Fun (Int, Pure, Int)))
    ; ("(lsr)", Fun (Int, Pure, Fun (Int, Pure, Int)))
    ; ("(asr)", Fun (Int, Pure, Fun (Int, Pure, Int)))
    ; (* Floating-point arithmetic *)
      (* String operations *)
      ("(^)", Fun (String, Pure, Fun (String, Pure, String)))
    ; (* Character operations *)
      (* Unit operations *)
      ( "ignore"
      , let a = Typevar (new_typevar ()) in
        Fun (a, Pure, Unit) )
    ; (* String conversion functions *)
      ("string_of_bool", Fun (Bool, Pure, String))
    ; ("bool_of_string", Fun (String, Mixed, Bool))
    ; ("string_of_int", Fun (Int, Pure, String))
    ; ("int_of_string", Fun (String, Mixed, Int))
    ; (* Pair operations *)
      (* List operations *)
      ( "(@)"
      , let a = Typevar (new_typevar ()) in
        Fun (List a, Pure, Fun (List a, Pure, List a)) )
    ; (* Input/output *)
      (* Output functions on standard output *)
      ("print_string", Fun (String, Output, Unit))
    ; ("print_int", Fun (Int, Output, Unit))
    ; ("print_endline", Fun (String, Output, Unit))
    ; ("print_newline", Fun (Unit, Output, Unit))
    ; (* Output functions on standard error *)
      (*   ("prerr_string",   Fun (String, (true,false), Unit));
           ("prerr_int",      Fun (Int, (true,false), Unit));
           ("prerr_endline",  Fun (String, (true,false), Unit));
           ("prerr_newline",  Fun (Unit, (true,false), Unit));    *)
      (* Input functions on standard input *)
      (* General output functions *)
      (* General input functions *)
      (* Operations on large files *)
      (* References *)
      (* Result type *)
      (* Operations on format strings *)
      (* Program termination *)
      ( "exit"
      , let a = Typevar (new_typevar ()) in
        Fun (Int, Exception, a) )
    ; (*   ("at_exit",        Fun (Fun (Unit, (true,false), Unit), (true,false), Unit)); *)
      (* More list operations from List module *)
      ( "List.hd"
      , let a = Typevar (new_typevar ()) in
        Fun (List a, Mixed, a) )
    ; ( "List.tl"
      , let a = Typevar (new_typevar ()) in
        Fun (List a, Mixed, List a) )
      (*   ("List.concat",    let a = Typevar (new_typevar()) in
         			Fun (List (List a), Pure, List a)); *)
    ]
