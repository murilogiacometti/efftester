open QCheck
open Efftester
open Ast
open Generator
open Effects
open Tcheck

(** A classifier *)

let rec lit_size l =
  match l with
  | LitUnit | LitInt _ | LitBool _ | LitStr _ ->
      1
  | LitList ls ->
      List.length ls


let rec term_size e =
  match e with
  | Lit l ->
      lit_size l
  | Variable (_, _) ->
      1
  | Lambda (_, _, _, e) ->
      1 + term_size e
  | App (_, e, _, e', _) ->
      1 + term_size e + term_size e'
  | Let (_, _, e, e', _, _) ->
      1 + term_size e + term_size e'
  | If (_, e, e', e'', _) ->
      1 + term_size e + term_size e' + term_size e''
  | Try (e, _, e', _, _) ->
      1 + term_size e + term_size e'
  | Raise (e, _, _) ->
      1 + term_size e


let coll_gen =
  set_collect
    (fun e -> match e with None -> "0" | Some e -> string_of_int (term_size e))
    term_gen


let effect_types =
  set_collect
    (fun term_opt ->
      match term_opt with
      | None ->
          "none"
      | Some term ->
          let env, _, _ = init_tri_env in
          let _, effect = tcheck env term in
          eff_to_str effect)
    term_gen


let coltest =
  Test.make ~count:1000 (*1000*) coll_gen (fun _ ->
      print_char '.' ;
      flush stdout ;
      true)


let effect_types_test =
  Test.make ~count:1000 (*1000*) effect_types (fun _ ->
      print_char '.' ;
      flush stdout ;
      true)


;;
reset_var ()

;;
reset_typevar ()

;;
QCheck_runner.run_tests_main [ coltest; effect_types_test ]
