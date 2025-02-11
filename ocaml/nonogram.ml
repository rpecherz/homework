let ( let* ) xs ys = List.concat_map ys xs;;

let rec choose m n =
  if m > n then [] else m :: choose (m+1) n

let rec sum xs : int =
  let rec helper xs ans =
    match xs with
    | [] -> ans
    | x::xs' -> helper xs' (ans + x)
  in
  helper xs 0


(* tworzy liste o wartosci bool dlugosci n*)
let rec boollist b n : bool list = 
  match n with
  | 0 -> []
  | _ -> b::boollist b (n-1)


let build_row ps n : bool list list=
   match ps with 
   | [] | [0] -> [boollist false n]
   | [x] -> 
     if x = n then [boollist true n] 
     else 
       let maxi=(n+1-sum ps-List.length ps) in
       let* start= choose 0 maxi in
       [((boollist false start)@(boollist true x)@(boollist false (n-x-start)))]
   | x::ps' -> 
      let maxi=(n+1-sum ps-List.length ps) in
      let* start= choose 0 maxi in
      let akt=((boollist false start)@(boollist true x)) in
      let rec helper ps'' rest ans slot zwrot =
        match ps'' with 
        | [] ->
            if List.length ans = n then (ans::zwrot)
            else if List.length ans > n then zwrot
            else ((ans @ boollist false rest)::zwrot)
        | y::pss ->
            let* slot = choose 1 rest in
            let good = (boollist false slot)@(boollist true y) in 
            helper pss (rest-List.length good) (ans@good) slot zwrot
      in helper ps' (n+1-List.length ps-start) akt 1 [];;



let build_candidate pss n : bool list list list=
  let rec helper ps ans =
    match ps with 
    | [] -> [List.rev ans]
    | x::ps' -> 
      let* row = build_row x n in
      helper ps' (row::ans)
  in helper pss [] 
       
(* liczy ile true w calosci*)
let count_trues xs : int=
  let rec helper xs acc =
    match xs with
    | [] -> acc
    | b::xs' -> if b = true then helper xs' (acc + 1) else helper xs' acc
  in
  helper xs 0
(*sprawdza ile jest kolejnych true i zwraca (n - ich liczbe)*)
let rec checker n xs : int =
   match xs with 
    | [] -> n
    | x::xs' ->
     if x=true then checker (n-1) xs' else n 
(*zwraca liste ktorej pierwszym elementem jes true*)
let rec next_true xs : bool list =
 match xs with
 | []->[]
 | x::xs' -> 
 if x=true then xs else next_true xs'
(*zwraca liste ktorej pierwszym elementem jes false*)
let rec next_false xs : bool list =
 match xs with
 | []->[]
 | x::xs' -> 
 if x=false then xs else next_false xs'


let rec verify_row ps xs : bool =
  if count_trues xs <> sum ps then false else
  let rec helper ps xs =
    match ps with 
    | [] -> 
      if count_trues xs <> 0 then false else true
    | x::ps' ->
      let next=next_true xs in
      if checker x next <> 0 then false else helper ps' (next_false next)
   in helper ps xs


let rec verify_rows pss xss =
  match pss, xss with
  | [], [] -> true 
  | [], _ | _, [] -> false
  | ps :: pss', xs :: xss' -> 
    if verify_row ps xs && verify_rows pss' xss' then true else false

let transpose xss =
  let rec helper xss ans =
    match xss with
    | [] :: _ -> List.rev ans
    | _ ->
        let col = List.map List.hd xss in
        let rest = List.map List.tl xss in
        helper rest (col :: ans)
  in
  helper xss []




type nonogram_spec = {rows: int list list; cols: int list list};;

let solve_nonogram nono =
  build_candidate (nono.rows) (List.length (nono.cols))
  |> List.filter (fun xss -> transpose xss |> verify_rows nono.cols);;

let example_1 = 
{
  rows = [[2];[1];[1]];
  cols = [[1;1];[2]]
};;

let example_2 = 
{
  rows = [[2];[2;1];[1;1];[2]];

  cols = [[2];[2;1];[1;1];[2]]
};;

let big_example = 
{
  rows = [[1;2];[2];[1];[1];[2];[2;4];[2;6];[8];[1;1];[2;2]];
  cols = [[2];[3];[1];[2;1];[5];[4];[1;4;1];[1;5];[2;2];[2;1]]
};;