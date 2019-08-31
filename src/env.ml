open Ast

(** Enviroment type definitions and functions *)

module TypeSet = Set.Make (struct
  type t = etype

  let compare = Stdlib.compare
end)

module VarSet = Set.Make (struct
  type t = variable

  let compare = String.compare
end)

module VarMap = Map.Make (struct
  type t = variable

  let compare = String.compare
end)

module TypeMap = Map.Make (struct
  type t = etype

  let compare = Stdlib.compare
end)

let add_multimap key value map =
  (* assume key has been normalized *)
  try
    let s = TypeMap.find key map in
    let new_set = VarSet.add value s in
    TypeMap.add key new_set map
  with
  | Not_found ->
      TypeMap.add key (VarSet.singleton value) map


let remove_multimap key value map =
  (* assume key has been normalized *)
  let old_key_set = TypeMap.find key map in
  let fixed_old_type_set = VarSet.remove value old_key_set in
  if VarSet.is_empty fixed_old_type_set
  then TypeMap.remove key map
  else TypeMap.add key fixed_old_type_set map


type tri_dir_env = etype VarMap.t * VarSet.t TypeMap.t * VarSet.t TypeMap.t

let poly_entry = Typevar (-1)

(* special entry Typevar (-1) holds all vars with polymorphic return type *)

let add_var var new_type (env, rev_env, return_env) =
  let env' = VarMap.add var new_type env in
  (* Overrides existing entry *)
  let old_type = try Some (VarMap.find var env) with Not_found -> None in
  let rev_env' =
    let fixed_rev_env =
      match old_type with
      | Some old_type ->
          remove_multimap old_type var rev_env
      | None ->
          rev_env
    in
    add_multimap new_type var fixed_rev_env
  in
  let return_env' =
    let rts = return_types new_type in
    let fixed_return_env =
      match old_type with
      | Some s ->
          List.fold_left
            (fun rEnv rt ->
              if ftv rt = []
                 (* return type polymorphic? Then syntactic comp. will not find it *)
              then remove_multimap rt var rEnv
              else remove_multimap poly_entry var rEnv)
            return_env
            (return_types s)
      | None ->
          return_env
    in
    List.fold_left
      (fun rEnv rt ->
        if ftv rt = []
           (* return type polymorphic? Then syntactic comp. will not find it *)
        then add_multimap rt var rEnv
        else add_multimap poly_entry var rEnv)
      fixed_return_env
      rts
  in
  (env', rev_env', return_env')


let lookup_var x (env, _, _) = try Some (VarMap.find x env) with Not_found -> None

let lookup_type s (_, rev_env, _) =
  try TypeMap.find s rev_env with Not_found -> VarSet.empty


let lookup_return s (env, _, return_env) =
  let concrete_set = try TypeMap.find s return_env with Not_found -> VarSet.empty in
  let arity_s = arity s in
  let rec has_compat_rt t =
    (arity t = arity_s && types_compat t s)
    ||
    match t with
    | Fun (_, _, rt) ->
        has_compat_rt rt
    | Typevar _ | Unit | Int | Bool | String | List _ | Exn ->
        false
  in
  let poly_set =
    VarSet.fold
      (fun x acc -> if has_compat_rt (VarMap.find x env) then VarSet.add x acc else acc)
      (try TypeMap.find poly_entry return_env with Not_found -> VarSet.empty)
      VarSet.empty
  in
  VarSet.union concrete_set poly_set
