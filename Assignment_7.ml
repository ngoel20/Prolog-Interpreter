open List;; 

type symbol = string
type tree = V of string | C of { node: symbol ; children: tree list }
type signature = (symbol * int) list

let check_sig (s : signature) = 
  let rec aux l acc =
    match l with
      [] -> true
    | h :: t -> let cond = (not (List.mem (fst h) acc)) && ((snd h) >= 0) in
        if cond then aux t ((fst h) :: acc)
        else false
  in
  aux s [] 
  
let rec wftree (t : tree) (s : signature) = match t with
    V _ -> true
  | C record -> 
      let check = fold_left (fun run ele -> run || ((record.node = fst ele) && (List.length record.children = snd ele))) false s in
      if check then fold_left (fun run subtree -> run && (wftree subtree s)) true record.children
      else false
        
let rec tree_equal (t1 : tree) (t2 : tree) = match t1, t2 with
    V x, V y -> x = y
  | C rec1, C rec2 ->
      if (rec1.node = rec2.node) then (fold_left (fun run ele -> run && (tree_equal (fst ele) (snd ele))) true (List.combine rec1.children rec2.children)) else false
  | _, _ -> false

let rec ht (t : tree) = match t with
    V _ -> 1
  | C record -> 
      let x = fold_left (fun run subtree -> max run (ht subtree)) 0 record.children in
      x + 1
      
let rec sz (t : tree) = match t with
    V _ -> 1
  | C record -> 
      let x = fold_left (fun run subtree -> run + (sz subtree)) 0 record.children in
      x + 1
      
let vars (t : tree) = 
  let rec aux t acc = match t with
      V str -> 
        if (List.mem str acc) then acc
        else (str :: acc)
    | C record -> fold_left (fun run subtree -> aux subtree run) acc record.children
  in
  aux t []

type substitution = (tree * tree) list
    
exception Invalid_substitution
    
let check_valid_subst (s : substitution) = 
  let rec aux given acc =
    match given with
      [] -> true
    | h :: t -> match fst h with
        V str -> 
          let cond = (not (List.mem str acc)) in
          if cond then aux t (str :: acc)
          else raise Invalid_substitution
      | _ -> raise Invalid_substitution
  in
  aux s []
    
let rec subst (s : substitution) (t : tree) : tree = 
  let rec aux s var = match s with
      [] -> var
    | head :: tail -> 
        if fst head = var then snd head
        else aux tail var
  in
  match t with 
    V _ -> aux s t
  | C record -> 
      let z = map (subst s) record.children in
      C {node = record.node ; children = z}

let compose_subst (s1 : substitution) (s2 : substitution) : substitution = 
  let upd_s1 = map (fun ele -> (fst ele, subst s2 (snd ele))) s1 in
  let v_s1 = map (fun ele -> fst ele) s1 in
  let extra_s2 = filter (fun ele -> not (List.mem (fst ele) v_s1)) s2 in
  upd_s1 @ extra_s2
  
exception NOT_UNIFIABLE
  
let rec mgu (t1 : tree) (t2 : tree) : substitution = 
  match t1, t2 with
    V str1, V str2 -> if str1 <> str2 then [(t1, t2)] else []
  | C rec1, C rec2 -> 
      if rec1.node <> rec2.node then raise NOT_UNIFIABLE
      else 
        let zip = List.combine rec1.children rec2.children in
        fold_left (fun run ele -> compose_subst run (mgu (subst run (fst ele)) (subst run (snd ele)))) [] zip
  | V str, C _ -> if List.mem str (vars t2) then raise NOT_UNIFIABLE else [(t1, t2)]
  | C _, V str -> if List.mem str (vars t1) then raise NOT_UNIFIABLE else [(t2, t1)]

type 'a set = 'a list

let emptyset = []

let member x s = 
  fold_left (fun run ele -> (ele = x) || run) false s 

let diff s1 s2 = 
  filter (fun ele -> not (member ele s2)) s1
  
let union s1 s2 = 
  let extra = diff s2 s1 in
  s1 @ extra 

type horn_clause = {head: tree; body: tree set};;

type program = horn_clause list;;

type goal = tree set;;

type 'a stack = 'a list;;

exception Error;;

(* let rec string_of_term (t : tree) : string =
  match t with
  | V str -> "var " ^ str
  | C { node; children } ->
      let child_strings = String.concat ", " (List.map string_of_term children) in
      Printf.sprintf "%s(%s)" node child_strings
let string_of_substitution (s : substitution) : string =
  let subst_strings = List.map (fun (var, replacement) -> Printf.sprintf "%s -> %s" (string_of_term var) (string_of_term replacement)) s in
  String.concat "; " subst_strings
let string_of_goal (g : goal) : string =
  let goal_strings = List.map string_of_term g in
  String.concat ", " goal_strings *)
  
let resolution (go : goal) (p : program) (sg : signature): (bool)*(substitution list) =
  if not (check_sig sg) then raise Error
  else 
    let wf_p_check = fold_left (fun run clse -> run && (wftree clse.head sg) && (fold_left (fun subrun subclse -> subrun && (wftree subclse sg)) true clse.body)) true p in
    let wf_g_check = fold_left (fun run clse -> run && (wftree clse sg)) true go in
    if not (wf_g_check && wf_p_check) then raise Error
    else

      let first (triple : 'a*'b*'c) = 
        match triple with
          (a, _, _) -> a in
      let second (triple : 'a*'b*'c) = 
        match triple with
          (_, b, _) -> b in
      let third (triple : 'a*'b*'c) = 
        match triple with
          (_, _, c) -> c in

      let n = List.length p in
      let rec aux (g : goal) (sub : substitution) (stk : ((tree set)*(substitution)*(int)) stack) (acc : substitution list) (line : int) = 
        (* Printf.printf "Current goals: %s\n" (string_of_goal g);
        Printf.printf "Current substitutions: %s\n" (string_of_substitution sub);
        Printf.printf "Current line: %d\n" line; *)
        if (line = n+1) then 
          match stk with
            [] -> acc
          | top :: rest -> aux (first top) (second top) rest acc ((third top) + 1)
        else
          match g with
            [] -> aux g sub stk (sub :: acc) (n+1) 
          | h::t -> 
              let temp = List.nth p (line-1) in
              try
                let unifier = (mgu temp.head h) in
                let newsub = compose_subst sub unifier in
                (* aux (union temp.body t) newsub ((g, sub, line) :: stk) acc 1 *)
                aux (union (map (fun ele -> subst unifier ele) temp.body) (map (fun ele -> subst unifier ele) t)) newsub ((g, sub, line) :: stk) acc 1
              with
              | NOT_UNIFIABLE -> 
                  (* Printf.printf "Not unifiable for line %d, trying next line.\n" line; *)
                  aux g sub stk acc (line+1)
      in
      let ans = aux go [] [] [] 1 in
      match ans with
        [] -> (false, [[]])
      | _ -> 
          (* map (fun xxx -> Printf.printf "Final substitutions: %s\n" (string_of_substitution xxx)) ans; *)
          let go_vars = fold_left (fun run ele -> union run ele) [] (map vars go) in
          (* map (fun s -> print_string (s ^ ", ")) go_vars; *)
          let ret = 
            map (fun lst -> 
                filter (fun ele -> 
                    (match ele with
                       (V str1, str2) -> 
                         (if member str1 go_vars then true 
                          else 
                            match str2 with
                              V s -> member s go_vars
                            | _ -> false)
                     | (_, _) -> false)) lst) ans in
          (true, List.rev ret)