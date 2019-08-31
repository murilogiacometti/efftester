open Ast
open Effects
open Env

let rec tcheck_lit l =
  match l with
  | LitUnit ->
      (Unit, Pure)
  | LitInt _ ->
      (Int, Pure)
  | LitBool _ ->
      (Bool, Pure)
  | LitStr _ ->
      (String, Pure)
  | LitList l ->
      let etyp =
        List.fold_left
          (fun typacc elem ->
            let etyp, _ = tcheck_lit elem in
            if types_compat typacc etyp (* if typacc is a generalization of etyp *)
            then etyp
            else if types_compat etyp typacc (* if etyp is a generalization of typeacc *)
            then typacc
            else failwith (type_message "tcheck_lit" etyp typacc "LitList"))
          (Typevar (new_typevar ()))
          l
      in
      (List etyp, Pure)


let rec tcheck env term =
  (* For each term, the annotated type may be more concrete then the type inferred by tcheck *)
  (* We should be able to obtain the annotated type by instantiating inferred type. *)
  (* For example, the annotation might contain "int list" and the inferred type might be "'a list" *)
  (* This function returns the most general type (?) *)
  match term with
  | Lit l ->
      tcheck_lit l
  | Variable (t, v) ->
    ( try
        let inferred_type = VarMap.find v env in
        if types_compat inferred_type t
        then (inferred_type, Pure)
        else failwith (type_message "tcheck" inferred_type t "Variable")
      with
    | Not_found ->
        failwith "tcheck: unknown variable" )
  | App (rt, m, at, n, effect) ->
      let mtyp, meff = tcheck env m in
      let ntyp, neff = tcheck env n in
      if meff = Pure || neff = Pure
      then
        if unified_types_compat ntyp at
        then
          match mtyp with
          | Fun (_, latent_eff, inferred_return) ->
              let inferred_effect = eff_app latent_eff meff neff in
              let annotated_fun = Fun (at, latent_eff, rt) in
              if unified_types_compat mtyp annotated_fun
              then
                if effects_compat inferred_effect effect
                then
                  if unified_types_compat inferred_return rt
                  then (inferred_return, inferred_effect)
                  else failwith (type_message "tcheck" inferred_return rt "App (Return)")
                else failwith (effect_message "tcheck" inferred_effect effect "App")
              else failwith (type_message "tcheck" mtyp annotated_fun "App (Left)")
          | Typevar _ ->
              let inferred_effect = eff_app Pure meff neff in
              if effects_compat inferred_effect effect
              then (mtyp, inferred_effect)
              else
                failwith (effect_message "tcheck" inferred_effect effect "App (Typevar)")
          | _ ->
              failwith "tcheck: application of non-function type"
        else failwith (type_message "tcheck" ntyp at "App (Right)")
      else failwith "tcheck: application has subexprs with eff"
  | Let (x, t, m, n, _type, effect) ->
      let mtyp, meff = tcheck env m in
      let ntyp, neff = tcheck (VarMap.add x mtyp env) n in
      let inferred_type = ntyp in
      let inferred_effect = eff_let meff neff in
      if unified_types_compat inferred_type _type
      then
        if effects_compat inferred_effect effect
        then (inferred_type, inferred_effect)
        else failwith (effect_message "tcheck" inferred_effect effect "Let")
      else failwith (type_message "tcheck" inferred_type _type "Let")
  | Lambda (t, x, s, m) ->
      let mtyp, meff = tcheck (VarMap.add x s env) m in
      let inferred_type = Fun (s, meff, mtyp) in
      if unified_types_compat inferred_type t
      then (inferred_type, Pure)
      else failwith (type_message "tcheck" inferred_type t "Lambda")
  | If (t, b, m, n, e) ->
      let btyp, beff = tcheck env b in
      let mtyp, meff = tcheck env m in
      let ntyp, neff = tcheck env n in
      let inferred_type = unify_and_subst mtyp ntyp in
      let inferred_effect = eff_if beff meff neff in
      if types_compat btyp Bool
      then
        if types_compat inferred_type t
        then
          if effects_compat inferred_effect e
          then (inferred_type, inferred_effect)
          else failwith (effect_message "tcheck" inferred_effect e "If")
        else failwith (type_message "tcheck" inferred_type t "Try")
      else failwith (type_message "tcheck" btyp Bool "Try (Conditional)")
  | Try (e1, x, e2, _type, effect) ->
      let e1_type, e1_effect = tcheck env e1 in
      let e2_type, e2_effect = tcheck (VarMap.add x Exn env) e2 in
      let inferred_type = unify_and_subst e1_type e2_type in
      let inferred_effect = eff_try e1_effect e2_effect in
      if types_compat inferred_type _type
      then
        if effects_compat inferred_effect effect
        then (inferred_type, inferred_effect)
        else failwith (effect_message "tcheck" inferred_effect effect "Try")
      else failwith (type_message "tcheck" inferred_type _type "Try")
  | Raise (e, typ, effect) ->
      let e_type, e_effect = tcheck env e in
      let inferred_effect = eff_raise e_effect in
      if types_compat e_type Exn
      then
        if effects_compat inferred_effect effect
        then (Typevar (new_typevar ()), inferred_effect)
        else failwith (effect_message "tcheck" e_effect effect "Raise")
      else failwith (type_message "tcheck" e_type Exn "Raise")


let rec tcheck' env term ?(lambdaVarType = Typevar (new_typevar ())) () =
  match term with
  | Lit l ->
      tcheck_lit l
  | Variable (_, v) ->
    ( try
        let inferred_type = VarMap.find v env in
        (inferred_type, Pure)
      with
    | Not_found ->
        failwith "tcheck: unknown variable" )
  | App (_, m, _, n, _) ->
      let ntyp, neff = tcheck' env n () in
      let mtyp, meff = tcheck' env m ~lambdaVarType:ntyp () in
      if meff = Pure || neff = Pure
      then
        match mtyp with
        | Fun (inferred_input, latent_eff, inferred_return) ->
            let inferred_effect = eff_app latent_eff meff neff in
            if unified_types_compat ntyp inferred_input
            then (inferred_return, inferred_effect)
            else
              failwith
                ( "tcheck: application types are not compatible "
                ^ type_to_str mtyp
                ^ "|"
                ^ type_to_str ntyp )
        | Typevar _ ->
            let inferred_effect = eff_app Pure meff neff in
            (mtyp, inferred_effect)
        | _ ->
            failwith "tcheck: application of non-function type"
      else failwith "tcheck: application has subexprs with eff"
  | Let (x, _, m, n, _, _) ->
      let mtyp, meff = tcheck' env m () in
      let ntyp, neff = tcheck' (VarMap.add x mtyp env) n () in
      let inferred_type = ntyp in
      let inferred_effect = eff_let meff neff in
      (inferred_type, inferred_effect)
  | Lambda (_, x, s, m) ->
      let mtyp, meff = tcheck' (VarMap.add x s env) m () in
      let inferred_type = Fun (s, meff, mtyp) in
      (inferred_type, Pure)
  | If (_, b, m, n, _) ->
      let btyp, beff = tcheck' env b () in
      let mtyp, meff = tcheck' env m () in
      let ntyp, neff = tcheck' env n () in
      let inferred_type = unify_and_subst mtyp ntyp in
      let inferred_effect = eff_if beff meff neff in
      if types_compat btyp Bool
      then (inferred_type, inferred_effect)
      else failwith (type_message "tcheck" btyp Bool "Try (Conditional)")
  | Try (e1, x, e2, _, _) ->
      let e1_type, e1_effect = tcheck' env e1 () in
      let e2_type, e2_effect = tcheck' (VarMap.add x Exn env) e2 () in
      let inferred_type = unify_and_subst e1_type e2_type in
      let inferred_effect = eff_try e1_effect e2_effect in
      (inferred_type, inferred_effect)
  | Raise (e, _, _) ->
      let e_type, e_effect = tcheck' env e () in
      let inferred_effect = eff_raise e_effect in
      if types_compat e_type Exn
      then (Typevar (new_typevar ()), inferred_effect)
      else failwith (type_message "tcheck" e_type Exn "Raise")
