(* abstract syntax tree *)

type bop = Mult | Div | Add | Sub | Eq | Lt | Gt | Leq | Geq | Neq
type ident = string

type expr =
  | Int of int
  | Bool of bool
  | Binop of bop * expr * expr
  | If of expr * expr * expr
  | Var of ident
  | Let of ident * expr * expr

module M = Map.Make(String)

type env = expr M.t
type zmienne = string M.t

(*sprawdza czy e1 i e2 sa alfa rownowazne*)
let rec alpha_equiv (e1 : expr) (e2 : expr) (env1w2 : zmienne) (env2w1 : zmienne) (env_e : env) : bool = 
  match e1, e2 with
  | Int n1, Int n2 -> n1 = n2
  | Bool b1, Bool b2 -> b1 = b2
  | Binop (op1, e1l, e1r), Binop (op2, e2l, e2r) ->
      op1 = op2 && alpha_equiv e1l e2l env1w2 env2w1 env_e && alpha_equiv e1r e2r env1w2 env2w1 env_e
  | If (p1, t1, e1),If (p2, t2, e2) ->
      alpha_equiv p1 p2 env1w2 env2w1 env_e && alpha_equiv t1 t2 env1w2 env2w1 env_e && alpha_equiv e1 e2 env1w2 env2w1 env_e
  | Var x1, Var x2 ->
      (match M.find_opt x1 env1w2, M.find_opt x2 env2w1 with
       | Some x, Some y -> x1 = y && x2 = x
       | None, None -> 
           if x1 <> x2 then false else
             (match M.find_opt x1 env_e, M.find_opt x2 env_e with
              | Some x, Some y -> x = y
              | None, None -> true 
              | _ -> false)    
       | _ -> false)
  | Let (x1, e1l, e1r), Let (x2, e2l, e2r) ->
      alpha_equiv e1l e2l (M.add x1 x2 env1w2) (M.add x2 x1 env2w1) env_e && alpha_equiv e1r e2r env1w2 env2w1 env_e
  | _ -> false

(*tworzy unikalna nazwe zmiennej*)
let name used : string =
  let rec helper (last : string) =        
    if List.mem last used then helper (last ^ "#") 
    else last                                       
  in helper ("#")

(*wrzuca do srodowiska env_e(calego wyrazenia) wszystkie zmienne zwiazane*)
let rec bound_env (e : expr) (env_e : env) : env = 
    match e with 
    | Int _ | Bool _ | Var _ -> env_e
    | Binop (_,e1,e2) -> bound_env e2 (bound_env e1 env_e)
    | If (p,t,e) -> bound_env p (bound_env t (bound_env e env_e))
    | Let (x,e1,e2) ->
        bound_env e2 (M.add x e1 env_e)

(*zwraca liste zmiennych z xs bez powtorek*)
let rec only_one (xs : string list) : string list =
  match xs with
  | [] -> []
  | x :: xs' ->
      (match List.mem x xs' with
       |false -> (x::(only_one xs'))
       |true -> only_one xs')

(*Funkcja wywolujaca funkcje name dla kazdej zwiazanej zmiennej*)
let rename (e : expr) : expr = 
  let rec helper (e : expr) (used : string list) (env : env): expr =
    match e with 
    | Int n -> Int n 
    | Bool b -> Bool b 
    | If (x, t, f) ->
        If (helper x used env, helper t used env, helper f used env)
    | Binop (op, e1, e2) ->
        Binop (op, helper e1 used env, helper e2 used env)
    | Var x -> 
        (match M.find_opt x env with
         | Some v -> v 
         | None -> Var x)
    | Let (x, e1, e2) ->
        let new_name = name used in
        Let (new_name, helper e1 (new_name :: used) env, helper e2 (new_name :: used) (M.add x (Var new_name) env))
  in helper e [] M.empty

(*done*)
(*zbiera wszystke expr ktore sa kandydatami do bycia przypisanym do leta i tworzy z nich liste *)
let make_candidates (e : expr) : expr list = 
  let rec helper (e : expr) (acc : expr list): expr list = 
    match e with 
    | Int _ | Bool _ | Var _ -> acc
    | Binop (op, e1, e2) -> 
        (e :: helper e1 (helper e2 acc))
    | If (x,t,f) -> 
        (e :: helper f (helper t (helper x acc)))
    | Let (_, e1, e2) -> 
         (e :: helper e1 (helper e2 acc))
  in helper e []


(*szuka pierwszej pary podwyrazen alpha rownowaznych*)
let rec alpha_search (xs : expr list) (env_e) : expr list = 
  match xs with 
  | [] -> []
  | [x1] -> []
  | x :: xs' ->
      let rec helper (e : expr) (candidates : expr list) (matches : expr list) : expr list= 
        match candidates with 
        | [] -> 
            (match matches with 
             | [] -> alpha_search xs' env_e
             | _ -> matches )
        | y :: candidates' -> 
            (match alpha_equiv e y M.empty M.empty env_e with
             | false -> helper e candidates' matches
             | true -> helper e candidates' (y :: matches))
      in helper x xs' []

(*zamienia wartosci alfa rownowazne z odpowiedzia dla Let "0#0" *)
let rec alpha_to_ans (e : expr) (ans : expr) (env_e : env) : expr =
  match e with 
  | Int _ | Bool _ | Var _ -> e
  | Binop (op, e1, e2) -> 
      if alpha_equiv e ans M.empty M.empty env_e 
      then Var "0#0" 
      else Binop (op, alpha_to_ans e1 ans env_e, alpha_to_ans e2 ans env_e)
  | If (p,t,el) -> 
      if alpha_equiv e ans M.empty M.empty env_e 
      then Var "0#0"
      else If (alpha_to_ans p ans env_e, alpha_to_ans t ans env_e, alpha_to_ans el ans env_e)
  | Let (x, e1, e2) -> 
      if alpha_equiv e ans M.empty M.empty env_e 
      then Var "0#0"
      else Let (x, alpha_to_ans e1 ans env_e, alpha_to_ans e2 ans env_e)  


(* 2. Wolne wystapienia zmiennych w wyrazeniach e1 i e2 sa wolne takze w e*)
(*tworzy liste wsyzstkich zmiennych z podwyrazenia *)
let e_var (e : expr) (env_e) : string list = 
  let rec helper (e : expr) (ans : string list) =
    match e with 
    | Int _ | Bool _ -> ans
    | Binop (op, e1, e2) -> helper e2 (helper e1 ans)
    | Let (x, e1, e2)-> helper e2 (helper e1 ans)
    | If (p, t, f) -> helper p (helper t (helper f ans))
    | Var x ->  
        (match M.find_opt x env_e with
         | Some v -> (x :: ans)
         | None -> ans)
  in helper e []

(* funkcja cse*)
let cse (e : expr) : expr option=
  let e2 = rename e in 
  (*env_e to srodowisko calego wyrazenia*)
  let env_e = bound_env e2 M.empty in
  let candidates = make_candidates e2 in 
  let alm_ans = alpha_search candidates env_e in 
  match alm_ans with 
  | [] -> None 
  | y :: xs' -> 
	let rec helper (e : expr) : expr option =
      	let variables = only_one (e_var y env_e) in
      	let bound_vars = only_one (e_var e env_e) in
      	  match e with
          | Binop (op, e1, e2) ->
             if List.for_all (fun x -> List.mem x variables) bound_vars
             then Some (Let ("0#0", y, alpha_to_ans e y env_e))
             else
              (match helper e1, helper e2 with
               | Some e1', Some e2' -> Some (Binop (op, e1', e2'))
               | _ -> None)
          | If (p, t, f) ->
             if List.for_all (fun x -> List.mem x variables) bound_vars
             then Some (Let ("0#0", y, alpha_to_ans e y env_e))
             else
              (match helper p, helper t, helper f with
               | Some v1, Some v2, Some v3 -> Some (If (v1, v2, v3))
               | _ -> None)
          | Let (x, e1, e2) ->
             if List.for_all (fun x -> List.mem x variables) bound_vars
             then Some (Let ("0#0", y, alpha_to_ans e y env_e))
             else
              (match helper e1, helper e2 with
               | Some e1', Some e2' -> Some (Let (x, e1', e2'))
               | _ -> None)
          | _ -> failwith "not implemented"
         in helper e2

        