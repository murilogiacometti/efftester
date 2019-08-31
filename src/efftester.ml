(** *************************************************************** *)

(** OCaml compiler backend tester                                   *)

(** Initial version by Patrick Kasting and Mathias Nygaard Justesen *)

(** Type and effect extension by Jan Midtgaard                      *)

(** Exception effects extension by Murilo Giacometti Rocha          *)

(** *************************************************************** *)

open QCheck
open Ast
open Generator
open Shrinker
open Effects
open Tcheck
open Str

(** Compilation *)

(* Write OCaml source to file *)
let write_prog src filename =
  let ostr = open_out filename in
  let () = output_string ostr src in
  close_out ostr


let run srcfile compname compcomm runcomm =
  let exefile = "testdir/" ^ compname in
  let exitcode = Sys.command (Printf.sprintf compcomm srcfile exefile) in
  (* Check that compilation was successful *)
  if exitcode <> 0
  then
    failwith (compname ^ " compilation failed with error code " ^ string_of_int exitcode)
  else
    (* Run the compiled program *)
    let runcode =
      Sys.command (Printf.sprintf runcomm exefile ^ " >" ^ exefile ^ ".out 2>&1")
    in
    (runcode, exefile ^ ".out")


let read_file filename =
  let lines = ref [] in
  let channel = open_in filename in
  let lines_rev =
    try
      while true do
        lines := input_line channel :: !lines
      done ;
      !lines
    with
    | End_of_file ->
        close_in channel ;
        List.rev !lines
  in
  match lines_rev with
  | [] ->
      ""
  | head :: tail ->
      List.fold_left (fun s1 s2 -> s1 ^ " " ^ s2) head tail


let get_matches str pattern =
  (* TODO(murocha): Replace the implementation by a more efficient *)
  List.map
    (fun s ->
      match s with
      | Str.Delim s' ->
          s'
      | Str.Text _ ->
          failwith "get_matches: Unexpected mapping")
    (List.filter
       (fun s -> match s with Str.Delim _ -> true | Str.Text _ -> false)
       (Str.full_split (Str.regexp pattern) str))


let files_equivalent filename1 filename2 =
  let file1 = read_file filename1 in
  let file2 = read_file filename2 in
  let throw_pattern = ".*throw" in
  let exception_pattern = "'[A-Za-z_]*'" in
  if file1 = file2
  then true
  else if Str.string_match (Str.regexp throw_pattern) file1 0
          && Str.string_match (Str.regexp throw_pattern) file2 0
  then get_matches file1 exception_pattern = get_matches file2 exception_pattern
  else false


let equivalence (compname1, compcomm1, runcomm1) (compname2, compcomm2, runcomm2) src =
  (* Write OCaml source to file *)
  let file1 = Printf.sprintf "testdir/%s.ml" compname1 in
  let file2 = Printf.sprintf "testdir/%s.ml" compname2 in
  let () = write_prog src file1 in
  let () = write_prog src file2 in
  let nrun = run file1 compname1 compcomm1 runcomm1 in
  let brun = run file2 compname2 compcomm2 runcomm2 in
  match (nrun, brun) with
  | (ncode, nout), (bcode, bout) ->
      let comp = files_equivalent nout bout in
      let res = ncode = bcode && comp in
      if res
      then (
        print_string "." ;
        flush stdout ;
        res )
      else (
        print_string "x" ;
        flush stdout ;
        res )


let native_byte_equivalence src =
  (* -w -5@20-26 *)
  (* Silence warnings for partial applications *)
  (*                      and unused variables *)
  equivalence
    ("native", "ocamlopt -O3 -w -5-26-20 %s -o %s", "./%s")
    ("byte", "ocamlc -w -5-26-20 %s -o %s", "./%s")
    src


let js_of_ocaml_bucklescript_equivalence src =
  equivalence
    ( "js_of_ocaml"
    , "ocamlfind ocamlc -w -5-26-20 -package js_of_ocaml -package js_of_ocaml.ppx \
       -linkpkg -o testdir/temp.byte %s && js_of_ocaml testdir/temp.byte -o %s"
    , "node %s" )
    ("bucklescript", "bsc -w -5-26-20 %s -o %s", "node %s")
    src


let print_wrap t =
  Let
    ( "i"
    , Int
    , t
    , App
        ( Unit
        , Variable (Fun (Int, Output, Unit), "print_int")
        , Int
        , Variable (Int, "i")
        , Output )
    , Unit
    , Output )


let term_gen =
  make
    ~print:(Print.option (term_to_ocaml ~typeannot:false))
    (*       ~shrink:shrinker *)
    (list_permute_term_gen_rec_wrapper init_tri_env Int Mixed)


(* Initial goal here! *)

let type_gen =
  make
    ~print:type_to_str
    Gen.(
      frequency
        [ (1, map (fun i -> Typevar i) (oneofl [ 1; 2; 3; 4; 5 ])); (6, sized type_gen) ])


let term_gen_shrink = set_shrink shrinker term_gen

let unify_funtest =
  Test.make
    ~count:1000
    ~name:"types unify correctly"
    (pair type_gen type_gen)
    (fun (ty, ty') ->
      match unify ty ty' with
      | No_sol ->
          ty <> ty'
      | Sol t ->
          let sty = subst t ty in
          let sty' = subst t ty' in
          types_compat sty sty' || types_compat sty' sty)


let gen_classify =
  Test.make
    ~count:1000
    ~name:"classify gen"
    (make ~collect:(fun t -> if t = None then "None" else "Some") term_gen.gen)
    (fun _ ->
      let () =
        print_string "." ;
        flush stdout
      in
      true)


let ocaml_test =
  Test.make
    ~count:500
    ~name:"generated term passes OCaml's typecheck"
    term_gen_shrink
    (fun t_opt ->
      t_opt
      <> None
      ==>
      match t_opt with
      | None ->
          false
      | Some t ->
        ( try
            let () =
              print_string "." ;
              flush stdout
            in
            let file = "testdir/ocamltest.ml" in
            let () = write_prog (term_to_ocaml t) file in
            0 = Sys.command ("ocamlc -w -5-20@21-26 " ^ file)
          with
        | Failure _ ->
            false ))


let tcheck_test =
  Test.make
    ~count:500
    ~name:"generated term type checks"
    term_gen
    (*_shrink*)
    (fun t_opt ->
      t_opt
      <> None
      ==>
      match t_opt with
      | None ->
          false
      | Some term ->
          let env, _, _ = init_tri_env in
          print_string "." ;
          flush stdout ;
          ( try
              let _type, effect = tcheck' env term () in
              unified_types_compat _type Int && eff_leq effect Mixed
            with
          | _ ->
              false ))


let eq_test =
  Test.make ~count:100 ~name:"bytecode/native backends agree" term_gen (fun topt ->
      topt
      <> None
      ==>
      match topt with
      | None ->
          false
      | Some t ->
          native_byte_equivalence (term_to_ocaml (print_wrap t)))


let eq_test_js =
  Test.make ~count:100 ~name:"js_of_ocaml/bucklescript agree" term_gen (fun topt ->
      topt
      <> None
      ==>
      match topt with
      | None ->
          false
      | Some t ->
          js_of_ocaml_bucklescript_equivalence (term_to_ocaml (print_wrap t)))

(* The actual call to QCheck_runner.run_tests_main is located in effmain.ml *)
