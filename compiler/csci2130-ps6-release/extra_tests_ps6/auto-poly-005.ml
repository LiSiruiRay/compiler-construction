let comp = fun f -> fun g -> fun x -> f (g x) in comp (fun z -> 2) (fun k -> 4)
