
open Mlish_ast

exception TypeError
let type_error(s:string) = raise TypeError

type type_env = (var * tipe_scheme) list

let freshvar_counter = ref 0
let freshvar () : tvar = 
  let v = !freshvar_counter in 
  freshvar_counter := v + 1;
  "a" ^ string_of_int v

let union xs ys = 
  List.fold_left (fun acc x -> if List.mem x acc then acc else x::acc) ys xs

let minus xs ys = 
  List.filter (fun x -> not (List.mem x ys)) xs

let rec guesses_of_tipe (t:tipe) : tipe list = 
  match t with 
  | Guess_t({contents=None}) -> [t]
  | Guess_t({contents=Some t'}) -> guesses_of_tipe t'
  | Fn_t(t1,t2) | Pair_t(t1, t2) -> union (guesses_of_tipe t1) (guesses_of_tipe t2)
  | List_t(t1) -> guesses_of_tipe t1
  | _ -> []

let guesses_of_scheme (Forall(_,t)) = guesses_of_tipe t

let guesses_of_env (env:type_env): tipe list = 
  List.fold_left(fun acc (_,s) -> union (guesses_of_scheme s) acc) [] env

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
  | Forall(vs, t) -> 
    let b = List.map (fun a -> (a, Guess_t(ref None))) vs in
    let rec inst t = match t with 
      | Tvar_t v -> (try List.assoc v b with Not_found -> t)
      | Fn_t(t1, t2) -> Fn_t(inst t1, inst t2)
      | Pair_t(t1, t2) -> Pair_t(inst t1, inst t2)
      | List_t t1 -> List_t(inst t1)
      | Guess_t tr -> (match !tr with None -> t | Some t' -> inst t')
      | _ -> t
    in inst t

let generalize (env:type_env) (t:tipe) : tipe_scheme = 
  let t_gs = guesses_of_tipe t in 
  let env_gs = guesses_of_env env in
  let diff = minus t_gs env_gs in
  let gs_vs = List.map (function
  | Guess_t(g) -> (g, freshvar())
  | _ -> failwith "Expected only Guess_t in diff"
  ) diff 
  in
  let tc  = subst_guess gs_vs t in 
  Forall(List.map snd gs_vs, tc) 

  let rec unify (t1:tipe) (t2:tipe) : unit =
    match t1, t2 with
    | Int_t, Int_t | Bool_t, Bool_t | Unit_t, Unit_t -> ()
    | Fn_t (a1, b1), Fn_t (a2, b2) ->
        unify a1 a2; unify b1 b2
    | Pair_t (a1, b1), Pair_t (a2, b2) ->
        unify a1 a2; unify b1 b2
    | List_t t1, List_t t2 -> unify t1 t2
    | Guess_t ({contents = Some t1'}), t2 -> unify t1' t2
    | t1, Guess_t({contents = Some t2'}) -> unify t1 t2'
    | Guess_t ({contents = None} as r1), Guess_t ({contents = None} as r2) ->
        if r1 == r2 then () else r2 := Some t1
    | Guess_t ({contents = None} as r), t
    | t, Guess_t ({contents = None} as r) ->
        if occurs_check r t then type_error "occurs check failed" else r := Some t
    | Tvar_t a, Tvar_t b when a = b -> ()
    | _ -> type_error "type mismatch"

  and occurs_check r t = 
    match t with
    | Guess_t r' when r == r' -> true  
    | Guess_t {contents = None} -> false
    | Guess_t {contents = Some t'} -> occurs_check r t'
    | Fn_t (t1, t2) | Pair_t (t1, t2) -> occurs_check r t1 || occurs_check r t2
    | List_t t1 -> occurs_check r t1 
    | _ -> false

let infer_prim (p : prim) (arg_types : tipe list) : tipe =
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
      let a = Guess_t (ref None) in
      List_t a

  | Cons, [h; t] ->
      unify t (List_t h); List_t h

  | IsNil, [t] ->
      let a = Guess_t (ref None) in
      unify t (List_t a); Bool_t

  | Hd, [t] ->
      let a = Guess_t (ref None) in
      unify t (List_t a); a

  | Tl, [t] ->
      let a = Guess_t (ref None) in
      unify t (List_t a); List_t a

  | Int _, [] -> Int_t
  | Bool _, [] -> Bool_t
  | Unit, [] -> Unit_t

  | _ -> type_error "bad primitive application"
  


let rec infer_exp (env:type_env) ((e,_):exp) : tipe =
  match e with
  | Var x ->
    (try instantiate (List.assoc x env)
      with Not_found -> type_error ("unbound variable "^x))

  | PrimApp (prim, args) -> 
    let arg_types = List.map (infer_exp env) args in
    infer_prim prim arg_types

  | Fn (x, body) ->
    let arg_type = Guess_t (ref None) in
    let body_type = infer_exp ((x, Forall([], arg_type)) :: env) body in
    Fn_t (arg_type, body_type)

  | App (e1, e2) ->
    let t1 = infer_exp env e1 in
    let t2 = infer_exp env e2 in
    let result = Guess_t (ref None) in
    unify t1 (Fn_t(t2, result));
    result

  | If (cond, e1, e2) ->
    unify (infer_exp env cond) Bool_t;
    let t1 = infer_exp env e1 in
    unify t1 (infer_exp env e2);
    t1

  | Let (x, e1, e2) ->
    let t1 = infer_exp env e1 in
    let scheme = generalize env t1 in
    infer_exp ((x, scheme) :: env) e2


let type_check_exp (e:Mlish_ast.exp) : tipe = infer_exp [] e 