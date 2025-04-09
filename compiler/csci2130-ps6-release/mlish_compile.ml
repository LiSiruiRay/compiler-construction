module ML = Mlish_ast
module S = Scish_ast

exception ImplementMe

let rec compile_exp ((e,_):ML.exp) : S.exp = 
  match e with
  | ML.Var x -> S.Var x
  | ML.PrimApp (prim, e_list) -> 
    let e_list' = List.map compile_exp e_list in
    (* let _ = print_endline "checking point: ML.App(e1,e2)-> " in *)
    (match prim, e_list' with
       | ML.Int i, [] -> 
        (* let _ = print_endline "checking point: ML.App(e1,e2)-> " in *)
        S.Int i
       | ML.Bool b, [] -> S.Int (if b then 1 else 0)
       | ML.Unit , _ -> S.Int 0
       | ML.Plus, [a;b] -> S.PrimApp(S.Plus,[a;b])
       | ML.Minus,[a;b]-> S.PrimApp(S.Minus,[a;b])
       | ML.Times, [a;b] -> 
        
        (* let _ = print_endline "ML.Times, [a;b] -> " in *)
        
        S.PrimApp(S.Times, [a;b])
       | ML.Div, [a;b] ->  S.PrimApp(S.Div, [a;b])
       | ML.Eq, [a;b] -> S.PrimApp(S.Eq, [a;b])
       | ML.Lt, [a;b] -> 
        (* let _ = print_endline "checking point: ML.App(e1,e2)-> " in *)
        
        
        S.PrimApp(S.Lt, [a;b])

       | ML.Pair,[a;b] -> 
        (* let _ = print_endline "checking point: ML.App(e1,e2)-> " in *)
          S.PrimApp(S.Cons, [a; b])
      
       | ML.Fst,[a] -> S.PrimApp(S.Fst,[a])
       | ML.Snd,[a] -> S.PrimApp(S.Snd,[a])
    
       | ML.Nil, [] -> S.PrimApp(S.Cons, [S.Int 0; S.Int 0])
       | ML.Cons, [h;t] -> S.PrimApp(S.Cons, [S.Int 1; S.PrimApp(S.Cons, [h; t])])
        
      | ML.IsNil, [a] -> 
      
        S.PrimApp(S.Eq, [S.PrimApp(S.Fst, [a]); S.Int 0])
      
      | ML.Hd, [a] -> 
          S.If(S.PrimApp(S.Eq, [S.PrimApp(S.Fst, [a]); S.Int 1]),
              S.PrimApp(S.Fst, [S.PrimApp(S.Snd, [a])]),  
              S.Int 0)
      
      | ML.Tl, [a] -> 
          S.If(S.PrimApp(S.Eq, [S.PrimApp(S.Fst, [a]); S.Int 1]),
              S.PrimApp(S.Snd, [S.PrimApp(S.Snd, [a])]),  
              S.PrimApp(S.Cons, [S.Int 0; S.Int 0]))
              
       | _ -> failwith "Invalid primitive application"
    )
    | ML.Fn(x,e) -> 

      (* let _ = print_endline "checking point: " in *)
        S.Lambda(x, compile_exp e)
      
    | ML.App(e1,e2) -> 
       (* let _ = print_endline "checking point: " in *)

        let e1' = compile_exp e1 in
         (* let _ = print_endline "checking point: " in *)
        let e2' = compile_exp e2 in
        S.App(e1', e2')
            
    | ML.If(c,t,e) -> 
        let c' = compile_exp c in
        let t' = compile_exp t in
         (* let _ = print_endline "checking point: " in *)
        let e' = compile_exp e in
        S.If(c', t' ,e')
        
    | ML.Let(x,e1,e2) -> 
       (* let _ = print_endline "checking point: " in *)
      S.sLet x (compile_exp e1) (compile_exp e2)