type var = string   (* program variables *)
type tvar = string  (* type variables *)
type pos = int

type tipe = 
  Tvar_t of tvar
| Int_t
| Bool_t
| Unit_t
| Fn_t of tipe * tipe
| Pair_t of tipe * tipe
| List_t of tipe
| Guess_t of tipe option ref

type tipe_scheme = Forall of (tvar list) * tipe

type prim = 
  Int of int
| Bool of bool
| Unit   (* unit value -- () *)
| Plus   (* add two ints *)
| Minus  (* subtract two ints *)
| Times  (* multiply two ints *)
| Div    (* divide two ints *)
| Eq     (* compare two ints for equality *)
| Lt     (* compare two ints for inequality *)
| Pair   (* create a pair from two values *)
| Fst    (* fetch the 1st component of a pair *)
| Snd    (* fetch the 2nd component of a pair *)
| Nil    (* the empty list *)
| Cons   (* create a list from two values *)
| IsNil  (* determine whether a list is Nil *)
| Hd     (* fetch the head of a list *)
| Tl     (* fetch the tail of a list *)

type rexp = 
  Var of var
| PrimApp of prim * exp list
| Fn of var * exp
| App of exp * exp
| If of exp * exp * exp
| Let of var * exp * exp
and exp = rexp * pos

(**********************************************************)
(* Pretty printing                                        *)
(**********************************************************)

let pptvarcounter = ref 0;;
let ppfreshtvar () : string = 
  let curcount = !pptvarcounter in
  pptvarcounter := (curcount +1);
  "ptvar"^(string_of_int curcount)


(* let rec tipe2string (t:tipe):string = 
  match t with
    Tvar_t tvar -> "'" ^ tvar
  | Int_t -> "int"
  | Bool_t -> "bool"
  | Unit_t -> "unit"
  | Fn_t (t1, t2) -> "(" ^ tipe2string t1 ^ ") -> (" ^ tipe2string t2 ^ ")"
  | Pair_t (t1, t2) -> "(" ^ tipe2string t1 ^ ") * (" ^ tipe2string t2 ^ ")"
  | List_t t -> "(" ^ tipe2string t ^ ") list"
  | Guess_t tr ->
     match !tr with
     | None ->
        let tvar = ppfreshtvar () in
        let ty = Tvar_t tvar in
        (* let new_tr = Some ty in *)
        tr := Some ty;
        tipe2string ty
     | Some t -> tipe2string t *)
     let rec tipe2string (t:tipe):string = 
      match t with
        Tvar_t tvar -> "'" ^ tvar
      | Int_t -> "int"
      | Bool_t -> "bool"
      | Unit_t -> "unit"
      | Fn_t (t1, t2) -> "(" ^ tipe2string t1 ^ ") -> (" ^ tipe2string t2 ^ ")"
      | Pair_t (t1, t2) -> "(" ^ tipe2string t1 ^ ") * (" ^ tipe2string t2 ^ ")"
      | List_t t -> "(" ^ tipe2string t ^ ") list"
      | Guess_t tr ->
         match !tr with
         | None -> "(Guess)"
         | Some t -> tipe2string t



     let prim2string p = 
      match p with
      | Int i -> string_of_int i
      | Bool b -> if b then "true" else "false"
      | Unit -> "()"
      | Plus -> "+"
      | Minus -> "-"
      | Times -> "*"
      | Div -> "/"
      | Eq -> "="
      | Lt -> "<"
      | Pair -> "pair"
      | Fst -> "fst"
      | Snd -> "snd"
      | Nil -> "nil"
      | Cons -> "cons"
      | IsNil -> "isnil"
      | Hd -> "hd"
      | Tl -> "tl"
    
    let rec rexp2string (e:rexp) : string =
      match e with
      | Var x -> x
      | PrimApp(p, es) ->
          "(" ^ (prim2string p) ^ " " ^ (exps2string es) ^ ")"
      | Fn(x, e) -> "(fn " ^ x ^ " " ^ (exp2string e) ^ ")"
      | App(e1, e2) -> "(" ^ (exp2string e1) ^ " " ^ (exp2string e2) ^ ")"
      | If(e1, e2, e3) -> "(if " ^ (exp2string e1) ^ " " ^ (exp2string e2) ^ " " ^ (exp2string e3) ^ ")"
      | Let(x, e1, e2) -> "(let " ^ x ^ " = " ^ (exp2string e1) ^ " in " ^ (exp2string e2) ^ ")"
    
    and exp2string ((e, pos):exp) : string =
      (* Uncomment the next line if you want to show positions in the output *)
      (* "[" ^ string_of_int pos ^ "] " ^ *) rexp2string e
    
    and exps2string (es:exp list) : string =
      String.concat "; " (List.map exp2string es)
    
    let tipe_scheme2string (Forall (vars, t)) : string =
      if List.length vars > 0 then
        "forall " ^ (String.concat " " (List.map (fun v -> "'" ^ v) vars)) ^ ". " ^ tipe2string t
      else
        tipe2string t