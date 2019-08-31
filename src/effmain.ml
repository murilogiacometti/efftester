open Efftester
open Ast

;;
reset_var ()

;;
reset_typevar ()

;;
let tests = [ (*unify_funtest; gen_classify; ocaml_test; *) tcheck_test (*eq_test*) ] in
QCheck_runner.run_tests ~verbose:true tests
