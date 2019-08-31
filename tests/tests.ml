open OUnit2
open Ast
open Generator
open Effects

let test1 _ =
  assert_equal
    (Int, Pure)
    (let env, _, _ = init_tri_env in
     Ast.tcheck env (Lit (LitInt 1)))


let test2 _ =
  assert_equal
    (Fun (Int, Output, Unit), Pure)
    (let env, _, _ = init_tri_env in
     Ast.tcheck env (Variable (Fun (Int, Output, Unit), "print_int")))


let reverse_2_contains_reverse_try _ =
  assert_equal
    true
    (List.for_all
       (fun (effect1, effect2) -> eff_try effect1 effect2 = Output)
       (reverse_2 eff_try Output)) ;
  assert_equal
    true
    (List.for_all
       (fun (effect1, effect2) -> eff_try effect1 effect2 = Eval)
       (reverse_2 eff_try Eval))


let example _ =
  assert_equal
    ~printer:(fun (t, e) -> type_to_str t ^ " & " ^ eff_to_str e)
    (Int, Output)
    (let env, _, _ = init_tri_env in
     Ast.tcheck
       env
       (Try
          ( Let
              ( "n"
              , Fun (Unit, Pure, Unit)
              , Lambda (Fun (Unit, Pure, Unit), "t", Unit, Lit LitUnit)
              , Raise (Variable (Exn, "Not_found"), Pure)
              , Unit
              , Exception )
          , "d"
          , Let
              ( "j"
              , Unit
              , App
                  ( Unit
                  , Variable (Fun (Int, Output, Unit), "print_int")
                  , Int
                  , Lit (LitInt 4611686018427387903)
                  , Output )
              , App
                  ( Int
                  , Variable (Fun (Int, Pure, Int), "lnot")
                  , Int
                  , Lit (LitInt 9)
                  , Pure )
              , Int
              , Output )
          , Int
          , Output )))


(* Name the test cases and group them together *)
let suite =
  "suite"
  >::: [ "test1" >:: test1
       ; "test2" >:: test2
       ; "reverse_2_contains_reverse_try" >:: reverse_2_contains_reverse_try
       ; "example" >:: example
       ]


let () = run_test_tt_main suite
