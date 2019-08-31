type effect =
  | Eval
  | Mixed
  | Exception
  | Output
  | Pure

let eff_to_str eff =
  match eff with
  | Eval ->
      "eval"
  | Mixed ->
      "mixed"
  | Exception ->
      "exception"
  | Output ->
      "output"
  | Pure ->
      "pure"


let eff_leq eff1 eff2 =
  match (eff1, eff2) with
  | Pure, _
  | Output, Output
  | Output, Mixed
  | Output, Eval
  | Exception, Exception
  | Exception, Mixed
  | Exception, Eval
  | Mixed, Mixed
  | Mixed, Eval
  | Eval, Eval ->
      true
  | _, _ ->
      false


let eff_join eff1 eff2 =
  match (eff1, eff2) with
  | Eval, _ | _, Eval ->
      Eval
  | Pure, _ ->
      eff2
  | _, Pure ->
      eff1
  | Exception, Exception ->
      Exception
  | Output, Output ->
      Output
  | _, _ ->
      Mixed


let eff_promote eff1 eff2 =
  match (eff1, eff2) with Pure, _ -> eff2 | _, Pure -> eff1 | _, _ -> Eval


let eff_latent latent_eff eff_l eff_r =
  match (latent_eff, eff_l, eff_r) with
  | _, Exception, _ | _, _, Exception | _, Mixed, _ | _, _, Mixed ->
      Pure
  | _, _, _ ->
      latent_eff


let eff_app latent_eff eff_l eff_r =
  eff_join (eff_latent latent_eff eff_l eff_r) (eff_promote eff_l eff_r)


let eff_try eff_body eff_with =
  match (eff_body, eff_with) with
  | Pure, _ ->
      Pure
  | Output, _ ->
      Output
  | Eval, _ ->
      Eval
  | Exception, _ ->
      eff_with
  | Mixed, Pure | Mixed, Output ->
      Output
  | Mixed, Exception | Mixed, Mixed ->
      Mixed
  | Mixed, Eval ->
      Eval


let eff_let eff_bound eff_body =
  match (eff_bound, eff_body) with
  | Exception, _ | Mixed, _ ->
      eff_bound
  | _, _ ->
      eff_join eff_bound eff_body


let eff_if eff_cond eff1 eff2 =
  match (eff_cond, eff1, eff2) with
  | Exception, _, _ | Mixed, _, _ ->
      eff_cond
  | _, _, _ ->
      eff_join eff_cond (eff_join eff1 eff2)


let eff_raise eff = eff_join eff Exception
