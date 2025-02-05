(* file: main.ml
   author: Robert Muller, J. Tassarotti

  Problem set 0: exercises for coming up to speed in OCaml.

  Usage from parent directory:

   > dune exec bin/main.exe test

   Note that omitting "test" in the above won't run the tests.

   There are 10 problems worth 6 points total.

   1. isDigit (.25)
   2. newFileName (.25)
   3. homePath (.25)
   4. atoi (.25)
   5. tokenize (1)
   6. formatTree (1)
   7. subpalindrome (.75)
   8. listComparisons (.5)
   9. patience (1)
   10. FilteredSet module (.75)
*)

(* Problem 1: .25 points

   isDigit : char -> bool
*)
let isDigit (d: char): bool = 
  match d with
    | '0' -> true
    | '1' -> true
    | '2' -> true
    | '3' -> true
    | '4' -> true
    | '5' -> true
    | '6' -> true
    | '7' -> true
    | '8' -> true
    | '9' -> true
    | _ -> false;;

(* Problem 2: .25 points

   newFileName : string -> string -> string
*)
let newFileName (oldFileName: string) (newExtension: string) : string =
  match (String.rindex_opt oldFileName '.') with
    | Some v -> String.cat (String.sub oldFileName 0 (v + 1)) (newExtension)
    | None -> oldFileName;;
  (* failwith "Problem 2: newFileName not yet implemented." *)

(* Problem 3: .25 points

   homePath : unit -> string list
*)

open Unix;;
open String;;

let rec readdirListFromHandle (h: dir_handle) : string list =
  try match readdir h with
   | s -> s :: readdirListFromHandle h
with End_of_file -> [];;

let homePath () = split_on_char '/' (sub (getenv "HOME") 1 ((length (getenv "HOME")) - 1)) ;;
(* Unix.getenv "HOME";;

let test_path_handle = opendir "/Users/ray/rayfile/self-project/25s_class_proje/compiler/test_path";; *)
(* Problem 4: .25 points

   atoi : string -> int
*)
open String;;
open Char;;
let rec get_char_list (s: string) (i: int) : char list =
  try match get s i with
      | c -> c :: get_char_list s (i + 1)
  with Invalid_argument _ -> [];;

let to_int_single (c: char) : int = code c - code '0';;

let rec char_list_to_int_list (cl: char list) : int list =
  match cl with
  | [] -> []
  | a :: b -> to_int_single a :: char_list_to_int_list b;;

let rec get_reverse (l: int list): int list =
  match l with
  | [] -> []
  | a::b -> (get_reverse b) @ [a];;

let rec get_int_reverse (l : int list) =
  match l with
  | [] -> 0
  | a :: b -> a + 10 * get_int_reverse b;;

(* let rec get_int_value (sl: string list) (i: index) : int =
  try match sl.[i] with *)

 let atoi (s: string): int = (get_int_reverse (get_reverse (char_list_to_int_list (get_char_list s 0))));;
type token = If | And | Or

(* Problem 5: 1 points

   tokenize : string -> token list
*)

let rec extract_token (sl: string list) :string list=
match sl with
  | [] -> []
  | a::b ->
    match a with
    | "" -> extract_token b
    | _ -> a :: extract_token b;;


let str_to_token (s: string): token =
  match s with
    | "||" -> Or
    | "&&" -> And
    | "If" -> If
    | _ -> If;;

let rec list_str_to_token (sl: string list): token list =
  match sl with
    | [] -> []
    | a :: b -> str_to_token a :: list_str_to_token b;;
let tokenize (s: string): token list = list_str_to_token ((extract_token (split_on_char ' ' s)));;

(* Two problems related to trees. We have arrows as interior nodes
   and leaves that include a unique constant C and variables
   {v1, v2, ... }

               ->             ->
              /  \           /  \
            v0   ->         C    v1
                /  \
               C    C
 *)

(* Note that the 'too' field should probably be called 'to' (that is the names would be from and to), but 'to'
   is already a reserved keyword in OCaml, so we cannot use it for a field name. *)


(* Problem 6: 1 point

   formatTree : t -> string
*)
open Int;;

type t = C
       | Var of int
       | Arrow of { from : t
                  ; too  : t
                  };;

let rec t_to_str (tree: t) : string =
  match tree with
  | C -> "C"
  | Var i -> cat ("v") (to_string i)
  | Arrow {from = a; too = b} -> cat (cat "(" (cat (cat (t_to_str a) " -> ") (t_to_str b))) ")";;

let formatTree (tree: t): string = t_to_str tree;;
  (* failwith "Problem 6: formatTree not yet implemented." *)

(* Problem 7: .75 point 

   subplaindrome : string -> string
*)

(* let curr_max_subpalindrome (s: string) (index: int): int * string =
  let l = index in
  let r = index in
  if s.[l] = s.[r] then *)
(* open String;; *)
(* let rec curr_max_subpalindrome (s: string) (l: int) (r: int) : string =
  if (l < 0) || (r > (String.length s) - 1)  || ((String.get s l) != (String.get s r))
    then String.sub s (l + 1) (r - l - 1) else curr_max_subpalindrome s (l - 1) (r + 1);;
(* let rec curr_max_subpalindrome_odd (s: string) (l: int) (r: int) : string =
  if (l < 0) || (r > (String.length s) - 1)  || ((String.get s l) != (String.get s r))
    then String.sub s (l + 1) (r - l - 1) else curr_max_subpalindrome_odd s (l - 1) (r + 1);; *)
let rec get_max_subpalindrome (s: string) (index: int): string =
  if index = ((String.length s) - 1) then (Char.escaped (String.get s ((String.length s) - 1)))
  else let b = index in
      let next_max = get_max_subpalindrome s (index + 1) in
      let cur_odd  = curr_max_subpalindrome s b b in
      let cur_even = curr_max_subpalindrome s b (b + 1) in
      let next_max_len = String.length next_max in
      let cur_odd_len = String.length cur_odd in
      let cur_even_len = String.length cur_even in
      let max_val = max (max cur_odd_len cur_even_len) next_max_len in
      if max_val = next_max_len then next_max 
      else if max_val = cur_odd_len then cur_odd
      else cur_even;;  *)
let rec reverse_string (s: string) : string = 
  if String.length s <= 1 then s else let a = s in String.cat (reverse_string (String.sub s 1 (String.length s - 1)))  (Char.escaped (String.get a 0));;

let rec subpalindrome (s: string) = if s = reverse_string s then s else subpalindrome (String.sub s 1 (String.length s - 2));;
(* Problem 8: .5 point

   list_comparisons : int list -> comparison list
*)

(* let curr_max_subpalindrome_odd (s: string) (index: int) (prev_length: int): int * string =
  let l = index in
  let r = index in
    if !s.[l] = s.[r] then r - l - 1 else *)

type comparison = GEQ | LT;;

let rec listCompare (prev: int) (l: int list): comparison list =
  match l with
  | [] -> []
  | a :: b ->
    match (compare prev a) with
     | 1 -> LT :: listCompare a b (* prev > a *)
     | _ -> GEQ :: listCompare a b;;

let listComparisons (l: int list) : comparison list =
  match l with
    | [] -> []
    | a :: _ -> listCompare a l;;

(* Problem 9: 1 point

   patience : (int list) list -> int -> (int list) list
*)

(* let rec insert_as_list (index: int) (n: int) (l: (int list) list) (prev: (int list) list) : (int list) list =
  match index with
  | 0 -> prev @ [[n]] @ l
  | b ->
    match l with
     | [] -> prev @ [[n]]
     | a :: c -> insert_as_list (b - 1) (n) (c) (prev @ [a]);; *)
open List;;
let rec insert_as_list (index: int) (n: int) (l: (int list) list) (prev: (int list) list) : (int list) list =
  (* let ll = length l in *)
  if index = length l then l @ [[n]] else 
    if index = 0 then 
      match l with
          | [] -> prev @ [[n]]
          | curr :: rest -> prev @ [n :: curr] @ rest
    else 
      match l with
          | [] -> prev @ [[n]]
          | a :: c -> insert_as_list (index - 1) (n) (c) (prev @ [a]);; 
    (* match index with
      | 0 -> 
        match l with
          | [] -> prev @ [[n]]
          | curr :: rest -> prev @ [n :: curr] @ rest
      | b ->
        match l with
          | [] -> prev @ [[n]]
          | a :: c -> insert_as_list (b - 1) (n) (c) (prev @ [a]);; *)
(* match index with
| ll -> l @ [[n]]
| 0 -> 
  match l with
    | [] -> prev @ [[n]]
    | curr :: rest -> prev @ [n :: curr] @ rest
| b ->
  match l with
    | [] -> prev @ [[n]]
    | a :: c -> insert_as_list (b - 1) (n) (c) (prev @ [a]);; *)

(* let rec in *)
let rec get_index (l: int list) (n: int) (s: int) : int =
match l with
| [] -> s
| a :: b ->
  match Int.compare n a with
    | -1 -> s
    | 0 -> s
    | 1 -> get_index b n (s + 1)
    (* | 0 -> get_index b n (s + 1) *)
    | _ -> 100000000;;

let rec extract_int_list (l: (int list) list) : int list =
  match l with
    | [] -> []
    | a :: b -> 
      match a with 
        | [] -> extract_int_list b
        | c :: _ -> c :: extract_int_list b;;
        (* | c :: d ->  *)
        (* | [c] -> c :: extract_int_list b *)
        
let patience (l: (int list) list) (n: int) = 
  let extracted_list = extract_int_list l in
    let index = get_index extracted_list n 0 in
      insert_as_list index n l [];;

(* Problem 10 : .75 points *)

module type FilteredSetType = sig
  type t
  val newSet : (int -> bool) -> t
  val insert : int -> t -> t
  val member : int -> t -> bool
  val mapAndFilter : (int -> int) -> t -> t
end

module FilteredSet : FilteredSetType =
struct
  type t = ((int list) * (int -> bool))
  let newSet (f: (int -> bool)) = ([], f)
  let insert (n: int) (s: t) = 
    let (oldSet, f) = s in 
      match f(n) with
        | true -> (n :: oldSet, f)
        | false -> s
  let member (n: int) (s: t) = 
    let (oldSet, _) = s in
      List.mem n oldSet
  let rec mapAndFilter (g: int -> int) (s: t) = 
    let (oldSet, f) = s in
      match oldSet with
        | [] -> ([], f)
        | a :: b -> 
          match f(g(a)) with
            | true -> 
              let (rest, _) = mapAndFilter g (b, f) in 
              (g(a) :: rest, f)
            | false -> mapAndFilter g (b, f)

    (* let (oldSet, f) = s in
      match oldSet with
        | [] -> ([], g)
        | a :: b -> ([], g) *)
          (* match g(a) with 
            | true -> (a :: ) *)

end


(* TESTING **********************************************************)

type parts = One       (* isDigit *)
           | Two       (* newFileName *)
           | Three     (* homePath *)
           | Four      (* atoi *)
           | Five      (* tokenize *)
           | Six       (* formatTree *)
           | Seven       (* subpalindrome *)
           | Eight       (* listComparisons *)
           | Nine       (* patience *)
           | Ten       (* FilteredSet module *)

(* Some simple test data
*)
let v0 = Lib.fresh()
let v1 = Lib.fresh()
let v2 = Lib.fresh()

(*            t0 = ->        t1 = ->
                  /  \           /  \
                v0   ->         C    v1
                    /  \
                   C    C
*)
let t0 = Arrow { from = Var v0
               ; too  = Arrow { from = C
                              ; too  = C
                              }
               }

let t1 = Arrow { from = C
               ; too  = Var v1
               }

let t2 = Arrow { from = t1
               ; too  = Arrow { from = C
                              ; too  = C
                              }
               }
let t3 = Arrow { from = C
               ; too  = t0
               }

(********************************************************************)

(* Test isDigit
*)
let isDigitTest1 () = isDigit '0'
let isDigitTest2 () = isDigit '9'
let isDigitTest3 () = not (isDigit 'A')
let isDigitTests () =
  Lib.run_test "isDigit test1" isDigitTest1 ;
  Lib.run_test "isDigit test2" isDigitTest2 ;
  Lib.run_test "isDigit test3" isDigitTest3

(* Test newFileName
*)
let newFileNameTest1 () = newFileName "A.java" "class" = "A.class"
let newFileNameTest2 () = newFileName "A" "class" = "A"
let newFileNameTest3 () = newFileName "A.B.java" "class" = "A.B.class"
let newFileNameTest4 () = newFileName "A." "class" = "A.class"
let newFileNameTests () =
  Lib.run_test "newFileName test1" newFileNameTest1 ;
  Lib.run_test "newFileName test2" newFileNameTest2 ;
  Lib.run_test "newFileName test3" newFileNameTest3 ;
  Lib.run_test "newFileName test4" newFileNameTest4

(* Test homePath
*)
let homePathTest () =
  let answer = homePath () in
  let combiner name1 name2 = Lib.fmt "%s/%s" name1 name2 in
  let path = List.fold_left combiner "" answer
  in
  try
    Unix.chdir path = ()
  with
    Unix.Unix_error _ -> failwith "homeTest failed"
let homePathTests () = Lib.run_test "home test" homePathTest

(* Test atoi
*)
let atoiTest1 () = atoi "345" = 345
let atoiTest2 () = atoi "0" = 0
let atoiTests () =
  Lib.run_test "atoi test1" atoiTest1 ;
  Lib.run_test "atoi test2" atoiTest2

(* Test tokenize
*)
let tokenizeTest1 () =
  (tokenize "|| if && if && ") = [Or; If; And; If; And]
let tokenizeTest2 () = (tokenize "||") = [Or]
let tokenizeTest3 () = (tokenize "       ") = []
let tokenizeTests () =
  Lib.run_test "tokenize test1" tokenizeTest1 ;
  Lib.run_test "tokenize test2" tokenizeTest2 ;
  Lib.run_test "tokenize test3" tokenizeTest3

(* Test formatTree
*)
let formatTreeTest1 () = (formatTree t0) = "(v0 -> (C -> C))"
let formatTreeTest2 () = (formatTree t1) = "(C -> v1)"
let formatTreeTest3 () = (formatTree (Var v2)) = "v2"
let formatTreeTests () =
  Lib.run_test "formatTree test1" formatTreeTest1 ;
  Lib.run_test "formatTree test2" formatTreeTest2 ;
  Lib.run_test "formatTree test3" formatTreeTest3

(* Test subpalindrome
*)
let subpalindromeTest1 () = subpalindrome "aba" = "aba"
let subpalindromeTest2 () = subpalindrome "dabac" = "aba"
let subpalindromeTest3 () = subpalindrome "xx" = "xx"
let subpalindromeTest4 () = subpalindrome "x1amanaplanacanalpanamax1" = "amanaplanacanalpanama"
let subpalindromeTest5 () = subpalindrome "civic" = "civic"
let subpalindromeTest6 () = subpalindrome "deified" = "deified"
let subpalindromeTest7 () = subpalindrome "2eifie+" = "eifie"
let subpalindromeTest8 () = subpalindrome "xyz" = "y"
let subpalindromeTest9 () = subpalindrome "" = ""
let subpalindromeTests () =
  Lib.run_test "subpalindrome test1" subpalindromeTest1 ;
  Lib.run_test "subpalindrome test2" subpalindromeTest2 ;
  Lib.run_test "subpalindrome test3" subpalindromeTest3 ;
  Lib.run_test "subpalindrome test4" subpalindromeTest4 ;
  Lib.run_test "subpalindrome test5" subpalindromeTest5 ;
  Lib.run_test "subpalindrome test6" subpalindromeTest6 ;
  Lib.run_test "subpalindrome test7" subpalindromeTest7 ;
  Lib.run_test "subpalindrome test8" subpalindromeTest8 ;
  Lib.run_test "subpalindrome test9" subpalindromeTest9

let listComparisonsTest1 () = listComparisons [3] = [GEQ]
let listComparisonsTest2 () = listComparisons [3;4;5] = [GEQ; GEQ; GEQ]
let listComparisonsTest3 () = listComparisons [1;-1;1] = [GEQ; LT; GEQ]
let listComparisonsTest4 () = listComparisons [-1;-1;1] = [GEQ; GEQ; GEQ]
let listComparisonsTest5 () = listComparisons [9;8;7] = [GEQ; LT; LT]
let listComparisonsTest6 () = listComparisons [9;8;7;10] = [GEQ; LT; LT; GEQ]
let listComparisonsTests () =
  Lib.run_test "listComparisons test1" listComparisonsTest1 ;
  Lib.run_test "listComparisons test2" listComparisonsTest2 ;
  Lib.run_test "listComparisons test3" listComparisonsTest3 ;
  Lib.run_test "listComparisons test4" listComparisonsTest4 ;
  Lib.run_test "listComparisons test5" listComparisonsTest5 ;
  Lib.run_test "listComparisons test6" listComparisonsTest6 

let patienceTest1 () = patience [[3]] 4 = [[3]; [4]]
let patienceTest2 () = patience [] 3 = [[3]]
let patienceTest3 () = patience [[4]; [5]] 3 = [[3;4]; [5]]
let patienceTest4 () = patience [[2]; [6]] 4 = [[2]; [4;6]]
let patienceTest5 () = patience [[2]; [6]; [10]] 8 = [[2]; [6]; [8; 10]]
let patienceTest6 () = patience [[2]; [6]; [10]] 12 = [[2]; [6]; [10]; [12]]
let patienceTest7 () = patience [[2]; [3;6]; [10]] 3 = [[2]; [3;3;6]; [10]]
let patienceTest8 () = patience [[2]; [3]; [4]; [5]; [6]] 4 = [[2]; [3]; [4;4]; [5]; [6]]
let patienceTests () =
  Lib.run_test "patience test1" patienceTest1 ;
  Lib.run_test "patience test2" patienceTest2 ;
  Lib.run_test "patience test3" patienceTest3 ;
  Lib.run_test "patience test4" patienceTest4 ;
  Lib.run_test "patience test5" patienceTest5 ;
  Lib.run_test "patience test6" patienceTest6 ;
  Lib.run_test "patience test7" patienceTest7 ;
  Lib.run_test "patience test8" patienceTest8


let isEven n = (n mod 2 = 0)

open FilteredSet

let rec insert_list xs s =
  match xs with
  | [] -> s
  | x :: xs -> insert_list xs (insert x s)

let filteredSetTests_wrapper () =
  let evenSet_empty = newSet isEven in

  let evenSet_1 = insert_list [1;2;3;4;5;6] evenSet_empty in
  let evenSet_2 = insert_list [10;12;13] evenSet_empty in

  let lt5Set_empty = newSet ((>) 5) in

  let lt5Set_1 = insert_list [1;2;3;4;5;6] lt5Set_empty in
  let lt5Set_2 = mapAndFilter ((+) 2) lt5Set_1 in
  let filteredSetTest1 () = member 5 evenSet_1 = false in
  let filteredSetTest2 () = member 2 evenSet_1 = true in
  let filteredSetTest3 () = member 2 evenSet_2 = false in
  let filteredSetTest4 () = member 12 evenSet_2 = true in
  let filteredSetTest5 () = member 4 lt5Set_1 = true in
  let filteredSetTest6 () = member 5 lt5Set_1 = false in
  let filteredSetTest7 () = member 6 lt5Set_2 = false in
  let filteredSetTest8 () = member 4 lt5Set_2 = true in
  let filteredSetTest9 () = member 1 lt5Set_2 = false in
  Lib.run_test "filteredSet test1" filteredSetTest1 ;
  Lib.run_test "filteredSet test2" filteredSetTest2 ;
  Lib.run_test "filteredSet test3" filteredSetTest3 ;
  Lib.run_test "filteredSet test4" filteredSetTest4 ;
  Lib.run_test "filteredSet test5" filteredSetTest5 ;
  Lib.run_test "filteredSet test6" filteredSetTest6 ;
  Lib.run_test "filteredSet test7" filteredSetTest7 ;
  Lib.run_test "filteredSet test8" filteredSetTest8 ;
  Lib.run_test "filteredSet test9" filteredSetTest9

let filteredSetTests () =
  try filteredSetTests_wrapper () with
  | Failure s -> print_endline ("filteredSet tests error: `" ^ s ^ "`\n")
  | e -> print_endline ("filteredSet tests error: `" ^ Printexc.to_string e ^ "`\n")

(******************************************************************)

(******************************************************************)

let test part =
  match part with
  | One   -> isDigitTests()
  | Two   -> newFileNameTests()
  | Three -> homePathTests()
  | Four  -> atoiTests()
  | Five  -> tokenizeTests()
  | Six   -> formatTreeTests()
  | Seven   -> subpalindromeTests ()
  | Eight   -> listComparisonsTests ()
  | Nine -> patienceTests ()
  | Ten  -> filteredSetTests ()

let run () =
  let () = test One in
  let () = test Two in
  let () = test Three in
  let () = test Four in
  let () = test Five in
  let () = test Six in
  let () = test Seven in
  let () = test Eight in
  let () = test Nine in
  let () = test Ten in
  ()

let () =
  if (Array.length Sys.argv = 2 && Sys.argv.(1) = "test") then
    run ()
  else
    ()
