    (* util functions *)

let is_lower_case c =
  'a' <= c && c <= 'z'

let is_upper_case c =
  'A' <= c && c <= 'Z'

let is_alpha c =
  is_lower_case c || is_upper_case c

let is_digit c =
  '0' <= c && c <= '9'


let is_alphanum c =
  is_lower_case c ||
  is_upper_case c ||
  is_digit c

let is_blank c =
  String.contains " \012\n\r\t" c

let explode s =
  List.of_seq (String.to_seq s)

let implode ls =
  String.of_seq (List.to_seq ls)

let readlines (file : string) : string =
  let fp = open_in file in
  let rec loop () =
    match input_line fp with
    | s -> s ^ "\n" ^ (loop ())
    | exception End_of_file -> ""
  in
  let res = loop () in
  let () = close_in fp in
  res

    (* end of util functions *)

    (* parser combinators *)

type 'a parser = char list -> ('a * char list) option

let parse (p : 'a parser) (s : string) : ('a * char list) option =
  p (explode s)

let pure (x : 'a) : 'a parser =
  fun ls -> Some (x, ls)

let fail : 'a parser = fun ls -> None

let bind (p : 'a parser) (q : 'a -> 'b parser) : 'b parser =
  fun ls ->
    match p ls with
    | Some (a, ls) -> q a ls
    | None -> None

let (>>=) = bind
let (let*) = bind

let read : char parser =
  fun ls ->
    match ls with
    | x :: ls -> Some (x, ls)
    | _ -> None

let satisfy (f : char -> bool) : char parser =
  fun ls ->
    match ls with
    | x :: ls ->
        if f x then Some (x, ls)
        else None
    | _ -> None

let char (c : char) : char parser =
  satisfy (fun x -> x = c)

let seq (p1 : 'a parser) (p2 : 'b parser) : 'b parser =
  fun ls ->
    match p1 ls with
    | Some (_, ls) -> p2 ls
    | None -> None

let (>>) = seq

let seq' (p1 : 'a parser) (p2 : 'b parser) : 'a parser =
  fun ls ->
    match p1 ls with
    | Some (x, ls) ->
        (match p2 ls with
         | Some (_, ls) -> Some (x, ls)
         | None -> None)
    | None -> None

let (<<) = seq'

let alt (p1 : 'a parser) (p2 : 'a parser) : 'a parser =
  fun ls ->
    match p1 ls with
    | Some (x, ls)  -> Some (x, ls)
    | None -> p2 ls

let (<|>) = alt

let map (p : 'a parser) (f : 'a -> 'b) : 'b parser =
  fun ls ->
    match p ls with
    | Some (a, ls) -> Some (f a, ls)
    | None -> None

let (>|=) = map

let (>|) = fun p c -> map p (fun _ -> c)

let rec many (p : 'a parser) : ('a list) parser =
  fun ls ->
    match p ls with
    | Some (x, ls) ->
        (match many p ls with
         | Some (xs, ls) -> Some (x :: xs, ls)
         | None -> Some (x :: [], ls))
    | None -> Some ([], ls)

let rec many1 (p : 'a parser) : ('a list) parser =
  fun ls ->
    match p ls with
    | Some (x, ls) ->
        (match many p ls with
         | Some (xs, ls) -> Some (x :: xs, ls)
         | None -> Some (x :: [], ls))
    | None -> None

let rec many' (p : unit -> 'a parser) : ('a list) parser =
  fun ls ->
    match p () ls with
    | Some (x, ls) ->
        (match many' p ls with
         | Some (xs, ls) -> Some (x :: xs, ls)
         | None -> Some (x :: [], ls))
    | None -> Some ([], ls)

let rec many1' (p : unit -> 'a parser) : ('a list) parser =
  fun ls ->
    match p () ls with
    | Some (x, ls) ->
        (match many' p ls with
         | Some (xs, ls) -> Some (x :: xs, ls)
         | None -> Some (x :: [], ls))
    | None -> None

let whitespace : unit parser =
  fun ls ->
    match ls with
    | c :: ls ->
        if String.contains " \012\n\r\t" c
        then Some ((), ls)
        else None
    | _ -> None

let ws : unit parser =
  (many whitespace) >| ()

let ws1 : unit parser =
  (many1 whitespace) >| ()

let digit : char parser =
  satisfy is_digit

let natural : int parser =
  fun ls ->
    match many1 digit ls with
    | Some (xs, ls) ->
        Some (int_of_string (implode xs), ls)
    | _ -> None
    

let literal (s : string) : unit parser =
  fun ls ->
    let cs = explode s in
    let rec loop cs ls =
      match cs, ls with
      | [], _ -> Some ((), ls)
      | c :: cs, x :: xs ->
          if x = c
          then loop cs xs
          else None
      | _ -> None
    in loop cs ls

let keyword (s : string) : unit parser =
  (literal s) >> ws >| ()


    (* end of parser combinators *)
(* let error () : (string * string list) = ("Error", []) *)

(* There is definitely a parser-minded approach to the following 2 methods, but tail recursion is what came naturally *)
let is_number num = 
  let rec aux = fun ls accum ->
    if accum = false then false else
      match ls with
      | [] -> false
      | h :: [] -> is_digit h
      | h::t -> aux t (is_digit h)
  in aux (explode num) true

let is_name name = 
  let rec aux = fun ls accum ->
    if accum = false then false else
      match ls with
      | [] -> false
      | h :: [] -> is_alpha h or h = '_' or is_digit h
      | h :: t -> aux t (is_alpha h or is_digit h or h = '_')
  in 
  match (explode name) with
  | h :: t -> 
      if is_alpha h then aux t true
      else false
  | _ -> false




type const = CNat of int | CName of string | CUnit
                      
type com = 
  | Push of const
  | Trace
  | Add | Sub | Mul | Div
  | If of (prog * prog) | Else | End 

  (* Part 2 Definitions: *)
  | Let
  | Lookup
  | Begin of prog                 (* Terminated by End *)
  | FuncDef of (const * const * prog) (* Terminated by End *) 
  | Call

and prog = com list

type value = 
  | Nat of int 
  | Name of string 
  | Unit 
  | Error 
  | Func of string * string * prog * env

and env = (string * value) list 

let error () : (value list * string list) = ([Error], [])

let get_assoc (name : string) (e : env) : (value option) =
  List.assoc_opt name e 

let assoc (name : string) (v : value) (e : env) : env =
  (name, v) :: e
  (* match (get_assoc name e) with
  | Some _ -> (name, v) :: (List.remove_assoc name e)
  | None   -> (name, v) :: e *)

(* Only used for defining local environments for functions *)
let assoc_replace (name : string) (v : value) (e : env) : env =
  let rec aux = fun name v e accum ->
    match e with
    | (prev_name, prev_val) :: e ->
        if prev_name = name && prev_val != v then
          ((name, v) :: e) @ accum
        else
          aux name v e ((prev_name, prev_val) :: accum)
    | [] -> (name, v) :: accum 
  in aux name v e []


let parse_const =
  ws >>= fun _ ->
  ( (* parsing () (a unit) (see above function) *)
    keyword "()" >> pure CUnit
  ) <|>
  (
    natural >>= fun n -> pure (CNat n)
  ) <|>
  (
    let* first = (satisfy is_alpha) <|> (char '_') in 
    let* rest = many ((satisfy is_alphanum) <|> (char '_') <|> (char '\'')) in
    pure (CName (implode (first :: rest)))
  )

let parse_push = 
  ws >>= fun _ ->
  keyword "Push" >>= fun _ ->   
  parse_const >>= fun x ->
  ws >>= fun _ ->
  pure (Push x) 
        
let parse_trace =
  ws >>= fun _ ->
  keyword "Trace" >>= fun _ ->
  ws >>= fun _ ->
  pure (Trace)
        
let parse_add = 
  ws >>= fun _ ->
  keyword "Add" >>= fun _ ->
  ws >>= fun _ ->
  pure (Add)
        
let parse_sub =
  ws >>= fun _ ->
  keyword "Sub" >>= fun _ ->
  ws >>= fun _ ->
  pure (Sub)
    
let parse_mul = 
  ws >>= fun _ ->
  keyword "Mul" >>= fun _ ->
  ws >>= fun _ ->
  pure (Mul)
        
let parse_div =
  ws >>= fun _ ->
  keyword "Div" >>= fun _ ->
  ws >>= fun _ ->
  pure (Div)

(* Part 2: *)
let parse_let = 
  ws >>= fun _ ->
  keyword "Let" >>= fun _ ->
  ws >>= fun _ ->
  pure (Let)

let parse_lookup = 
  ws >>= fun _ ->
  keyword "Lookup" >>= fun _ ->
  ws >>= fun _ ->
  pure (Lookup)

let parse_call =
  ws >>= fun _ ->
  keyword "Call" >>= fun _ ->
  ws >>= fun _ ->
  pure (Call)
  
let rec command_parser () =
  ws >>= fun _ ->
  parse_push
  <|> parse_trace
  <|> parse_add
  <|> parse_sub
  <|> parse_mul
  <|> parse_div
  <|> parse_if ()

  (* Part 2: *)
  <|> parse_let
  <|> parse_lookup
  <|> parse_begin ()
  <|> parse_func ()
  <|> parse_call
  
and parse_if () =
  let* _ = keyword "If" in
  let* branch_t = (many (ws >> command_parser ())) in 
  let* _ = keyword "Else" in
  let* branch_f = (many (ws >> command_parser ())) in
  let* _ = keyword "End" in
  pure (If (branch_t, branch_f))
  

and prog_parser () : prog parser =
  let* com = command_parser () in
  let* prog =
    many (command_parser ())
  in pure (com :: prog) 

(* Part 2 mutually recursive parsers: *)
and parse_begin () =
  let* _ = keyword "Begin" in 
  let* cmds = (many (ws >> command_parser () )) in
  let* _ = keyword "End" in
  pure (Begin cmds)

and parse_func () =
  let* _ = keyword "Fun" in 
  let* fname = (ws >> parse_const) in
  let* arg   = (ws >> parse_const) in
  let* cmds  = (many (ws >> command_parser () )) in
  let* _ = keyword "End" in
  pure (FuncDef (fname, arg, cmds))
        
let string_of_const = fun cst ->
  match cst with
  | CNat y -> string_of_int y
  | CName y -> y
  | CUnit -> "()"

let string_of_val = fun v ->
  match v with
  | Nat y -> string_of_int y
  | Name y -> y
  | Unit -> "()"
  | Error -> "Error"
  | Func (fname, args, coms, env) -> fname ^ " " ^ args

let rec eval (p : prog) (s : value list) (e : env) (log : string list) : (value list * string list) = 
  match p, s with
  | Push CNat cst :: p, _  -> eval p (Nat cst :: s ) e log 
  | Push CName cst :: p, _ -> eval p (Name cst :: s) e log
  | Push CUnit :: p, _ -> eval p (Unit :: s) e log 

  | Trace :: p, popped :: s -> eval p (Unit :: s) e ((string_of_val popped) :: log)
  | Trace :: p, _ -> error ()

  | Add :: p, Nat v2 :: Nat v1 :: s -> eval p (Nat (v2 + v1) :: s) e log
  | Add :: p, _ -> error ()

  | Sub :: p, Nat v1 :: Nat v2 :: s -> eval p (Nat (v2 - v1) :: s) e log
  | Sub :: p, _ -> error ()

  | Mul :: p, Nat v2 :: Nat v1 :: s -> eval p (Nat (v2 * v1) :: s) e log
  | Mul :: p, _ -> error ()
    
  | Div :: p, Nat 0 :: _ :: s -> error ()
  | Div :: p, Nat v1 :: Nat v2 :: s -> eval p (Nat (v2 / v1) :: s) e log
  | Div :: p, _ -> error () 
                     
  | If (branch_t, branch_f) :: p, Nat v :: s ->
      if v > 0 then eval (branch_t @ p) s e log
      else eval (branch_f @ p) s e log
  | If (_, _) :: p, _ -> error () 


  | Else :: _, _ -> error ()
  | End :: _, _ -> error ()

  (* Part 2: *)
  | Let :: p, v :: Name nm :: s -> 
      let n_env = assoc nm v e in 
      eval p s n_env log
  | Let :: p, _ -> error ()

  | Lookup :: p, Name nm :: s -> 
      (
        match get_assoc nm e with
        | Some v  -> eval p (v :: s) e log
        | None    -> error ()
      )    
  | Lookup :: p, _ -> error ()

  | Begin cmds :: p, _ ->
      (
        match (eval cmds [] e log) with (* (stack, log) *)
        | Error :: _, _ -> error ()
        | v :: _, log2 -> eval p (v :: s) e (log2)
        | [], _ -> error ()

      )
  | Begin _ :: p, _ -> error ()

  | FuncDef (CName fname, CName arg, cmds) :: p, _ ->
      let func_env = assoc fname (Func (fname, arg, cmds, e)) e in
      let post_env = assoc_replace fname (Func (fname, arg, cmds, func_env)) e in
      eval p s post_env log
  | FuncDef _ :: p, _ -> error ()

  | Call :: p, arg :: Func (fname, func_arg, cmds, func_env) :: s -> 
      let func_def = Func (fname, func_arg, cmds, func_env) in
      let scope = assoc func_arg arg (assoc fname func_def func_env) in
      (
        match (eval cmds [] scope log) with (* v holds stack of function call *)
        | (v :: st, n_log) -> 
            if v = Error then error () else 
            eval p (v :: s) e n_log (* log overwritten *)
        | _ -> error ()
      )
  | Call :: p, _ -> error ()

  | [], s -> (s, log)



  (* Final match case: *)
  (* | [], x :: t -> (string_of_val x, log)
  | [], [] -> ("()", log) *)

let process (x : (value list * string list)) : (string * string list) =
  match x with
  | v :: _, log -> (string_of_val v, log)
  | _ -> ("Error", [])
        
    (* Interprets a program written in the Part1 Stack Language.
    * Required by the autograder, do not change its type. *)
let interpreter (s : string) : (string * string list) =
  match parse (prog_parser ()) s with
  | Some (prog, []) -> process (eval prog [] [] [])
  | _ -> ("Error", [])
  (* | Some (prog, []) -> 
    (
      match (eval prog [] [] []) with
      | Error, [] -> ("ur boy has an error", [])
      | v, log -> (string_of_val v, log)    
    )
  | _ -> ("error", []) *)