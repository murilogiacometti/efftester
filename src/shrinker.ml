open Ast
open Generator
open QCheck

let shrink_lit = function
  | LitInt i ->
      Iter.map (fun i' -> Lit (LitInt i')) (Shrink.int i)
  | LitStr s ->
      Iter.map (fun s' -> Lit (LitStr s')) (Shrink.string s)
  | LitList ls ->
      Iter.map (fun ls' -> Lit (LitList ls')) (Shrink.list ls)
  | _ ->
      Iter.empty


let ( <+> ) = Iter.( <+> )

let rec term_shrinker term =
  match term with
  | Lit l ->
      shrink_lit l
  | Variable (t, _) ->
    (match create_lit t with Some c -> Iter.return c | _ -> Iter.empty)
  | Lambda (t, x, s, m) ->
      Iter.map (fun m' -> Lambda (t, x, s, m')) (term_shrinker m)
  | App (rt, m, at, n, effect) ->
      ( match (create_lit rt, effect) with
      | Some c, Pure ->
          Iter.return c
      | _, _ ->
          Iter.empty )
      <+> (if types_compat at rt && imm_eff n = effect then Iter.return n else Iter.empty)
      <+> ( match m with
          | App (_, _, at', n', _) when types_compat at' rt && imm_eff n' = effect ->
              Iter.return n'
          | Lambda (_, x, s, m') ->
              Iter.empty
          | Let (x, t, m', n', _, _) ->
              Iter.empty
          | Raise (_, _, _) ->
              Iter.return m
          | _ ->
              Iter.empty )
      <+> (match n with Raise (_, _, _) -> Iter.return n | _ -> Iter.empty)
      <+> Iter.map (fun m' -> App (rt, m', at, n, effect)) (term_shrinker m)
      <+> Iter.map (fun n' -> App (rt, m, at, n', effect)) (term_shrinker n)
  | Let (x, t, m, n, s, e) ->
      (match create_lit s with Some c -> Iter.return c | _ -> Iter.empty)
      <+> ( match (fv x n, m) with
          | false, Let (x', t', m', _, _, _) ->
              Iter.empty
          | false, _ when imm_eff n = e ->
              Iter.return n
          | _, _ ->
              Iter.empty )
      <+> Iter.map (fun m' -> Let (x, t, m', n, s, e)) (term_shrinker m)
      <+> Iter.map (fun n' -> Let (x, t, m, n', s, e)) (term_shrinker n)
      <+> (match m with Raise (_, _, _) -> Iter.return m | _ -> Iter.empty)
  | If (t, b, m, n, e) ->
      (match (create_lit t, e) with Some c, Pure -> Iter.return c | _, _ -> Iter.empty)
      <+> Iter.map (fun b' -> If (t, b', m, n, e)) (term_shrinker b)
      <+> Iter.map (fun m' -> If (t, b, m', n, e)) (term_shrinker m)
      <+> Iter.map (fun n' -> If (t, b, m, n', e)) (term_shrinker n)
      <+> (match b with Raise (_, _, _) -> Iter.return b | _ -> Iter.empty)
  | Raise (e, _type, effect) ->
      Iter.map (fun e' -> Raise (e', _type, effect)) (term_shrinker e)
      <+> (match e with Raise (_, _, _) -> Iter.return e | _ -> Iter.empty)
  | Try (e1, x, e2, _type, effect) ->
      ( match (create_lit _type, effect) with
      | Some c, Pure ->
          Iter.return c
      | _, _ ->
          Iter.empty )
      <+> Iter.map (fun e1' -> Try (e1', x, e2, _type, effect)) (term_shrinker e1)
      <+> Iter.map (fun e2' -> Try (e1, x, e2', _type, effect)) (term_shrinker e2)
      <+>
      ( match (e1, fv x e2) with
      | Raise (_, _, Exception), false ->
          Iter.return e2
      | _, _ ->
          Iter.empty )


let wrapper shrinker opTerm =
  match opTerm with
  | None ->
      Iter.empty
  | Some term ->
      Iter.map (fun t -> Some t) (shrinker term)


let shrinker term = wrapper term_shrinker term
