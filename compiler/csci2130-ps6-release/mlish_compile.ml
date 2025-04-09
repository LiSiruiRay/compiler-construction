module ML = Mlish_ast
module S = Scish_ast

exception ImplementMe

let rec compile_exp ((e,_):ML.exp) : S.exp = 
  match e with
  | ML.Var x -> S.Var x
  | ML.PrimApp (prim, e_list) -> 
    (* let _ = print_endline "| ML.PrimApp (prim, e_list) -> " in *)
    let e_list' = List.map compile_exp e_list in
    (match prim, e_list' with
       | ML.Int i, [] -> S.Int i
       | ML.Bool b, [] -> S.Int (if b then 1 else 0)
       | ML.Unit , _ -> S.Int 0
       | ML.Plus, [a;b] -> S.PrimApp(S.Plus,[a;b])
       | ML.Minus,[a;b]-> S.PrimApp(S.Minus,[a;b])
       | ML.Times, [a;b] -> S.PrimApp(S.Times, [a;b])
       | ML.Div, [a;b] -> 
        (* let _ = print_endline "checking point" in *)
        S.PrimApp(S.Div, [a;b])
       
       | ML.Lt, [a;b] -> S.PrimApp(S.Lt, [a;b])
       | ML.Pair,[a;b] -> 
        
        (* let _ = print_endline "checking point: | ML.Pair,[a;b] -> " in *)
        S.PrimApp(S.Cons,[a;b])
       (* let _ = print_endline "checking point" in *)
       | ML.Nil,[] -> S.Int 0
       | ML.Fst,[a] -> S.PrimApp(S.Fst,[a])
       | ML.Eq, [a;b] -> S.PrimApp(S.Eq, [a;b])
       (* let _ = print_endline "checking point" in *)
       | ML.Snd,[a] -> S.PrimApp(S.Snd,[a])
       
       | ML.Cons,[h;t]-> S.PrimApp(S.Cons,[h;t])
       | ML.Tl,[a] -> 
        (* let _ = print_endline "checking point" in *)
        S.PrimApp(S.Snd, [a])
       | ML.IsNil,[a]-> 
        (* let _ = print_endline "checking point" in *)
        S.PrimApp(S.Eq,[a;S.Int 0])
       | ML.Hd,[a] -> S.PrimApp(S.Fst, [a])  

       
       | _ -> failwith "Invalid primitive application"
    )
  | ML.Fn(x,e) -> S.Lambda(x,compile_exp e)
  | ML.App(e1,e2)-> 
    (* let _ = print_endline "checking point: ML.App(e1,e2)-> " in *)
    S.App(compile_exp e1,compile_exp e2)
  | ML.If(c,t,e)-> S.If(compile_exp c,compile_exp t,compile_exp e)
  | ML.Let(x,e1,e2)-> S.sLet x (compile_exp e1) (compile_exp e2)