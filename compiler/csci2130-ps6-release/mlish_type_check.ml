open Mlish_ast

exception TypeError
let type_error(s:string) = raise TypeError

type type_env = (var * tipe_scheme) list

let type_env2string (env : type_env) : string =
  let binding2string (x, scheme) = 
    x ^ " : " ^ tipe_scheme2string scheme
  in
  "[" ^ (String.concat "; " (List.map binding2string env)) ^ "]"


let freshvar_counter = ref 0
let freshvar () : tvar = 
  let v = !freshvar_counter in 
  freshvar_counter := v + 1;
  "a" ^ string_of_int v

  (*Set Union*)
let union xs ys = 
  List.fold_left (fun acc x -> if List.mem x acc then acc else x::acc) ys xs

let minus xs ys =
  List.filter (fun x -> not (List.exists (fun y -> x == y) ys)) xs
  

let rec guesses_of_tipe (t:tipe) : tipe list = 
  (* let _= print_endline ("start of guesses_of_tipe: t: " ^ (tipe2string t)) in *)
  match t with 
  | Guess_t({contents=None}) -> [t]
  | Guess_t({contents=Some t'}) -> guesses_of_tipe t'
  | Fn_t(t1,t2) | Pair_t(t1, t2) -> union (guesses_of_tipe t1) (guesses_of_tipe t2)
  | List_t(t1) -> guesses_of_tipe t1
  | _ -> []

let guesses_of_scheme (Forall(_,t)) = guesses_of_tipe t

let guesses_of_env (env:type_env): tipe list = 
  List.fold_left(fun acc (_,s) -> union (guesses_of_scheme s) acc) [] env

(* substitute : (tvar * tipe) list * tipe -> tipe *)
let rec substitute (subs, t) =
  match t with
  | Int_t | Bool_t | Unit_t -> t
  | Tvar_t v ->
      (try List.assoc v subs with Not_found -> Tvar_t v)
  | Fn_t (t1, t2) ->
      Fn_t (substitute (subs, t1), substitute (subs, t2))
  | Pair_t (t1, t2) ->
      Pair_t (substitute (subs, t1), substitute (subs, t2))
  | List_t t' ->
      List_t (substitute (subs, t'))
  | Guess_t r ->
      (match !r with
       | Some t' -> substitute (subs, t')
       | None -> Guess_t r)
let rec subst_guess (subs:((tipe option ref) * tvar) list)(t:tipe) : tipe = 
  match t with 
  | Guess_t({contents=None} as g) -> 
    (try Tvar_t(List.assoc g subs) with Not_found -> Guess_t(g))
  | Guess_t({contents=Some t'}) -> subst_guess subs t'
  | Fn_t(t1, t2) -> Fn_t(subst_guess subs t1, subst_guess subs t2)
  | Pair_t(t1, t2) -> Pair_t(subst_guess subs t1, subst_guess subs t2)
  | List_t t1 -> List_t(subst_guess subs t1)
  | _ -> t

let instantiate (s:tipe_scheme) : tipe = 
  match s with 
  | Forall (vs, t) when vs <> [] ->
    let b = List.map (fun a -> (a, Guess_t(ref None))) vs in
    substitute (b, t)
    (* let rec inst t = match t with 
      | Tvar_t v -> (try List.assoc v b with Not_found -> t)
      | Fn_t(t1, t2) -> Fn_t(inst t1, inst t2)
      | Pair_t(t1, t2) -> Pair_t(inst t1, inst t2)
      | List_t t1 -> List_t(inst t1)
      | Guess_t tr -> (match !tr with None -> t | Some t' -> inst t')
      | _ -> t
    in inst t *)
  | Forall ([], t) -> t
  | _ -> failwith "probem happened in the instantiate"

(* let generalize (env:type_env) (t:tipe) : tipe_scheme = 
  let t_gs = guesses_of_tipe t in 
  let env_gs = guesses_of_env env in
  let diff = minus t_gs env_gs in
  let gs_vs = List.map (function
  | Guess_t(g) -> (g, freshvar())
  | _ -> failwith "Expected only Guess_t in diff"
  ) diff 
  in
  let tc  = subst_guess gs_vs t in 
  Forall(List.map snd gs_vs, tc)  *)

  let generalize (env:type_env) (t:tipe) : tipe_scheme = 
    let t_gs = guesses_of_tipe t in 
    let env_gs = guesses_of_env env in
    let diff = minus t_gs env_gs in
    let gs_vs = List.map (function
      | Guess_t(g) -> (g, freshvar())
      | _ -> failwith "Expected only Guess_t in diff"
    ) diff in
    let tc = subst_guess gs_vs t in
    (* Special handling for function types to ensure argument polymorphism *)
    (* let rec generalize_fn t = match t with
      | Fn_t(t1, t2) -> 
        let t1' = match t1 with
          | Guess_t({contents=None}) -> Tvar_t(freshvar())
          | _ -> t1
        in
        Fn_t(t1', generalize_fn t2)
      | _ -> t
    in
    let tc' = generalize_fn tc in *)
    Forall(List.map snd gs_vs, tc)

let rec norm t =
  match t with
  | Guess_t r ->
      (match !r with
        | Some t' -> norm t'
        | None -> t)
  | _ -> t
      let rec is_equal t1 t2 =
        let t1 = norm t1 in
        let t2 = norm t2 in
        match t1, t2 with
        | Int_t, Int_t -> true
        | Bool_t, Bool_t -> true
        | Unit_t, Unit_t -> true
        | Tvar_t v1, Tvar_t v2 -> v1 = v2
        | Fn_t (a1, b1), Fn_t (a2, b2) ->
            is_equal a1 a2 && is_equal b1 b2
        | Pair_t (a1, b1), Pair_t (a2, b2) ->
            is_equal a1 a2 && is_equal b1 b2
        | List_t t1, List_t t2 ->
            is_equal t1 t2
        | Guess_t r1, Guess_t r2 ->
            (* When both guesses are undetermined (i.e. not resolved),
               we compare the physical identity of the references. *)
            r1 == r2
        | _ -> false

    let rec unify (t1:tipe) (t2:tipe) : unit =
      let _ = print_endline ("in the let rec unify: checking type: \nt1: "^(tipe2string t1)^"\nt2: "^(tipe2string t2)) in
      if is_equal t1 t2 then () else
      (match t1, t2 with
      | Int_t, Int_t | Bool_t, Bool_t | Unit_t, Unit_t -> ()
    
      | Fn_t (a1, b1), Fn_t (a2, b2) ->
          unify a1 a2; unify b1 b2
      | Pair_t (a1, b1), Pair_t (a2, b2) ->
          unify a1 a2; unify b1 b2
      | List_t t1, List_t t2 -> unify t1 t2

      | Guess_t ({contents = Some t1'}), t2 -> unify t1' t2
    
      | Guess_t ({contents = None} as r), t ->
        if check_occurs r t then type_error "occurs check failed" else r := Some t
      
      | _, Guess_t (_) -> unify t2 t1
    
      | Tvar_t a, Tvar_t b when a = b -> ()
      
      | Tvar_t _, _ | _, Tvar_t _ -> ()  (* Allow unification with type variables *)
    
      | _ -> 
          (* let _ = print_endline "not reaching type error...." in *)
          type_error "type mismatch")

  and check_occurs r t = 
    match t with
    | Guess_t r' when r == r' -> true  
    | Guess_t {contents = None} -> false
    | Guess_t {contents = Some t'} -> check_occurs r t'
    | Fn_t (t1, t2) | Pair_t (t1, t2) -> check_occurs r t1 || check_occurs r t2
    | List_t t1 -> check_occurs r t1 
    | _ -> false

let prim_infer (p : prim) (arg_types : tipe list) : tipe =
  (* let _ = print_endline ("\n\n\n case: prim_infer: " ^ prim2string p) in *)
  (* let _ = print_endline ("Arg types: " ^ String.concat ", " (List.map tipe2string arg_types)) in *)

  match p, arg_types with
  | Plus, [t1; t2]
  | Minus, [t1; t2]
  | Times, [t1; t2]
  | Div, [t1; t2] ->
      unify t1 Int_t; unify t2 Int_t; Int_t

  | Eq, [t1; t2]
  | Lt, [t1; t2] ->
      unify t1 Int_t; unify t2 Int_t; Bool_t

  | Pair, [t1; t2] -> Pair_t(t1, t2)
  | Fst, [t] ->
      let a = Guess_t (ref None) in
      let b = Guess_t (ref None) in
      unify t (Pair_t(a, b)); a
  | Snd, [t] ->
      let a = Guess_t (ref None) in
      let b = Guess_t (ref None) in
      unify t (Pair_t(a, b)); b

      | Nil, [] ->
        (* let _ = print_endline ("\nin prim_infer case: | Nil, [] ->: ") in *)
        (* Create a new guess variable for the element type *)
        let elem_type = Guess_t (ref None) in
        (* let _ = print_endline ("\nend. prim_infer case: | Nil, [] ->: ") in *)
        List_t elem_type

  (* | Cons, [h; t] ->
      unify t (List_t h); List_t h *)
      | Cons, [h; t] ->
        (* let _ = print_endline ("\nin prim_infer case:  Cons, [h; t] -> ") in *)
        let elem_type = 
          match t with
          | List_t(Guess_t {contents=None}) -> 
              Guess_t(ref None)  
          | List_t(elem) -> elem 
          | _ -> Guess_t(ref None)
        in
        (* let _ = print_endline ("\nend..in prim_infer case:  Cons, [h; t] -> ") in *)
        unify h elem_type;
        unify t (List_t elem_type);
        List_t elem_type

  | IsNil, [t] ->
      let a = Guess_t (ref None) in
      unify t (List_t a); Bool_t

  | Hd, [t] ->
      let a = Guess_t (ref None) in
      unify t (List_t a); a

  | Tl, [t] ->
      let a = Guess_t (ref None) in
      unify t (List_t a); a

  | Int _, [] -> Int_t
  | Bool _, [] -> Bool_t
  | Unit, [] -> Unit_t

  | _ -> type_error "bad primitive application"
  


let rec type_infererence (env:type_env) (e_first :exp) : tipe =
  let (e,_) = e_first in
  let _ = print_endline "\n\nstart of type_infererence: " in
  let _ = print_endline ("type_env: "^(type_env2string env)) in
  let _ = print_endline ("e_first: "^(exp2string e_first)) in
  let _ = print_endline ("e: "^(rexp2string e)) in
  match e with
  | Var x ->
    (* let _ = print_endline ("\n\n\n -- case: | Var x -> \n") in *)
    (try instantiate (List.assoc x env)
      with Not_found -> type_error ("unbound variable "^x))

  | PrimApp (prim, args) -> 
    (* let _ = print_endline ("\n\n\n -- case: | PrimApp (prim, args) -> : \n") in *)

    (* let _ = print_endline ("args before call infer again: "^(exps2string args)) in *)
    (* let _ = print_endline ("before call infer again, prim: "^(prim2string prim)) in *)
    let mapping_func = type_infererence env in
    let arg_types = List.map mapping_func args in
    
    (* let _ = print_endline ("after calling: arg_types: "^(String.concat "; " (List.map tipe2string arg_types))) in *)
    (* let _ = print_endline ("end of | PrimApp (prim, args) -> ") in *)
    prim_infer prim arg_types

  | Fn (x, body) ->
    (* let _ = print_endline ("\n\n\n -- case: Fn (x, body), argument (x): "^(x)^", body: "^(exp2string body) )in *)
    let arg_type = Guess_t (ref None) in
    (* let _ = print_endline ("arg_type: "^(tipe2string arg_type) )in *)
    let new_env = ((x, Forall([], arg_type)) :: env) in
    (* let _ = print_endline ("checking new_env: " ^ (type_env2string new_env)) in *)
    let body_type = type_infererence new_env body in (*problem happened*)
    (* let _ = print_endline ("body_type: "^(tipe2string body_type) )in *)
    (* let _ = print_endline ("end of Fn Case ---- \n\n\n ") in *)
    Fn_t (arg_type, body_type)
    


  | App (e1, e2) ->
    (* let _ = print_endline ("\n\n\n -- case: App (e1, e2), "^"\ne1: "^(exp2string e1)^"\ne2: "^(exp2string e2))in *)
    let t1 = type_infererence env e1 in
    let t2 = type_infererence env e2 in
    
    let result = Guess_t (ref None) in
    (* let _= print_endline ("checking type: \ne1 (t1): "^(tipe2string t1)^"\ne2(t2): "^(tipe2string t2)) in *)
    (* let _ = print_endline "end of app case... \n\n " in *)
    unify t1 (Fn_t(t2, result));
    result

  | If (cond, e1, e2) ->
    let _ = print_endline ("\n\n\n -- case: If (cond, e1, e2)") in
    unify (type_infererence env cond) Bool_t;
    let t1 = type_infererence env e1 in
    let _ = print_endline ("checking point") in
    unify t1 (type_infererence env e2);
    t1

  | Let (x, e1, e2) ->
    (* let _ = print_endline ("\n\n\n -- case: Let (x, e1, e2), x: "^(x)^", \ne1: "^(exp2string e1)^", \ne2: "^(exp2string e2) )in *)
    let t1 = type_infererence env e1 in
    (* let _ = print_endline ("checking type, t1: "^(tipe2string t1))in *)
    let scheme = generalize env t1 in
    (* let _ = print_endline ("checking tipe_scheme2string, scheme: "^(tipe_scheme2string scheme))in *)
    (* let _ = print_endline "end of let case" in *)
    type_infererence ((x, scheme) :: env) e2


let type_check_exp (e:Mlish_ast.exp) : tipe = type_infererence [] e 
