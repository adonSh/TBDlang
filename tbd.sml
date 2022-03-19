(*
 * tbd.sml
 *   (c) 2021 Adon Shapiro
 *
 *)

datatype Obj = NIL
             | BOOL of bool
             | INT of int
             | SYM of string
             | QUOTE of Obj
             | QUEUE of Obj * Obj
             | CLOSURE of Obj   * Obj   * (string * Obj) list
            (* CLOSURE of QUEUE * QUEUE * Env *)
             | PRIMITIVE of Obj list * (string * Obj) list -> Obj list * (string * Obj) list
            (* PRIMITIVE of Stack    * Env                 -> Stack    * Env *)

type Stack = Obj list
type Env = (string * Obj) list

exception E      of string (* Errors that should be handled internally *)
exception Syntax of string (* Errors encountered during parsing *)
exception Eval   of string * Stack * Env (* Runtime errors *)
exception Abort  of int (* Exit immediately *)

(*** Parser ***)

fun charToInt c = Char.ord c - Char.ord #"0"

fun getChar (stream: TextIO.instream): char option = TextIO.input1 stream

fun peek (stream: TextIO.instream): char option = TextIO.lookahead stream

fun readNum n strm =
  case peek strm
    of NONE => n
     | SOME c => if Char.isDigit c
                 then readNum (n * 10 + (charToInt (valOf (getChar strm)))) strm
                 else n

fun validChar c = Char.isAlphaNum c orelse c = #"+" orelse c = #"-"
                                    orelse c = #"*" orelse c = #"/"
                                    orelse c = #"=" orelse c = #"."
                                    orelse c = #"<" orelse c = #">"

fun readSym s stream =
  let fun loop NONE = []
        | loop (SOME c) = if (validChar c)
                          then (valOf (getChar stream)) :: loop (peek stream)
                          else []
  in String.implode (s :: loop (peek stream))
  end

fun skipLine (stream: TextIO.instream): unit =
  case getChar stream
    of NONE => ()
     | SOME #"\n" => ()
     | SOME _ => skipLine stream

fun readQ end_sym stream: Obj =
  case read stream
    of NONE => raise Syntax "Premature EOF"
     | SOME (SYM s) => if s = end_sym
                       then NIL
                       else QUEUE (SYM s, readQ end_sym stream)
     | SOME ob => QUEUE (ob, readQ end_sym stream)

and read (stream: TextIO.instream): Obj option =
  case getChar stream
    of NONE => NONE
     | SOME c => if c = #" " orelse c = #"\t" orelse c = #"\r"
                             orelse c = #"\f" orelse c = #"\n"
                 then read stream
                 else if c = #";"
                 then (skipLine stream; read stream)
                 else if c = #"'"
                 then case read stream
                        of NONE => raise Syntax "Premature EOF"
                         | SOME (SYM "}") =>  raise Syntax "Unexpected }"
                         | SOME (SYM "]") =>  raise Syntax "Unexpected ]"
                         | SOME ob => SOME (QUOTE ob)
                 else if Char.isDigit c
                 then SOME (INT (readNum (charToInt c) stream))
                 else if c = #"]" then SOME (SYM "]")
                 else if c = #"}" then SOME (SYM "}")
                 else if (validChar c)
                 then SOME (SYM (readSym c stream))
                 else if c = #"["
                 then case read stream
                        of NONE => raise Syntax "Premature EOF"
                         | SOME (SYM "]") => SOME NIL
                         | SOME ob => SOME (QUEUE (ob, readQ "]" stream))
                 else if c = #"{"
                 then case read stream
                        of NONE => raise Syntax "Premature EOF"
                         | SOME NIL => SOME (readQ "}" stream)
                         | SOME (QUEUE q) => SOME (QUEUE
                                                    (QUOTE (QUEUE q),
                                                    QUEUE
                                                      (QUOTE (readQ "}" stream),
                                                      QUEUE
                                                        (SYM "MAKEFN",
                                                        NIL))))
                         | _ =>  raise Syntax "Malformed function"
                 else  raise Syntax "Invalid syntax"

(*** Evaluator ***)

fun repr NIL = "[]"
  | repr (QUOTE ob) = "'" ^ repr ob
  | repr (PRIMITIVE _) = "<primitive>"
  | repr (CLOSURE _)  = "<function>"
  | repr (BOOL true) = "true"
  | repr (BOOL false) = "false"
  | repr (SYM s) = s
  | repr (INT n) = if n < 0
                   then "-" ^ Int.toString (Int.abs n)
                   else Int.toString n
  | repr (QUEUE q) =
      let fun loop (QUEUE (h, NIL)) = repr h
            | loop (QUEUE (h, QUEUE t)) = repr h ^ " " ^ (loop (QUEUE t))
            | loop (QUEUE (h, t)) = repr h ^ " . " ^ (loop t)
            | loop _ = raise E "Not a valid queue"
      in "[" ^ (loop (QUEUE q)) ^ "]"
      end

fun find [] _ = NONE
  | find ((k, v) :: env: Env) sym = if sym = k then SOME v else find env sym

fun mkEnv NIL stk = (stk, [])
  | mkEnv (QUEUE (SYM _, _)) [] = raise E "Too few arguments"
  | mkEnv (QUEUE (SYM s, tail)) (ob :: stk) =
      let val (stk', env) = mkEnv tail stk
      in (stk', (s, ob) :: env)
      end
  | mkEnv _ _ = raise E "Invalid arguments list"

fun apply (PRIMITIVE p) stk env = p (stk, env)
  | apply (CLOSURE (args, body, env)) stk globalEnv =
      (let val (stk', env') = mkEnv args stk
       in case apply body [NIL] (env' @ env @ globalEnv)
            of (result :: _, _) => (result :: stk', globalEnv)
             | _ => (NIL :: stk', globalEnv)
       end
       handle E err => raise Eval (err, stk, globalEnv))
  | apply (QUEUE (head, NIL)) stk env = eval head stk env
  | apply (QUEUE (head, tail)) stk env =
      let val (stk', env') = eval head stk env
      in apply tail stk' env'
      end
  | apply (SYM s) stk env = (case find env s
                               of NONE => raise Eval ("Undefined symbol " ^ s, stk, env)
                                | SOME ob => apply ob stk env)
  | apply x s e = raise Eval (repr x ^ " is not an applicable object", s, e)

and eval NIL stk env = (NIL :: stk, env)
  | eval (QUOTE ob) stk env = (ob :: stk, env)
  | eval (BOOL b) stk env = (BOOL b :: stk, env)
  | eval (INT n) stk env = (INT n :: stk, env)
  | eval (QUEUE q) stk env = (case apply (QUEUE q) [NIL] env
                                of (result :: _, env') => (result :: stk, env')
                                 | (_, env') => (stk, env'))
  | eval (PRIMITIVE p) stk env = apply (PRIMITIVE p) stk env
  | eval (CLOSURE f) stk env = apply (CLOSURE f) stk env
  | eval (SYM "exit") (INT n :: _) _ = raise Abort n
  | eval (SYM "exit") (SYM s :: _) env = (case find env s
                                            of SOME (INT n) => raise Abort n
                                             | _ => raise Abort 0)
  | eval (SYM "exit") _ _ = raise Abort 0
  | eval (SYM s) stk env = case find env s
                             of NONE => raise Eval ("Undefined symbol: " ^ s, stk, env)
                              | SOME (QUEUE q) => (QUEUE q :: stk, env)
                              | SOME ob => eval ob stk env

(*** Primitives and Special Forms ***)

fun primDef (SYM v :: SYM k :: stk, env) =
      (case find env v
         of NONE => raise Eval ("Undefined symbol: " ^ v, stk, env)
          | SOME ob => (SYM k :: stk, (k, ob) :: env))
  | primDef (v :: SYM k :: stk, env) = (SYM k :: stk, (k, v) :: env)
  | primDef (stk, env) = raise Eval ("Two arguments required for def", stk, env)

fun primAdd (INT x :: INT y :: stk, env) = (INT (y + x) :: stk, env)
  | primAdd (INT x :: SYM s :: stk, env) =
      (case find env s
         of NONE => (INT x :: SYM s :: stk, env)
          | SOME ob => primAdd (INT x :: ob :: stk, env))
  | primAdd (INT x :: stk, env) = (INT x :: stk, env)
  | primAdd (SYM s :: stk, env) =
      (case find env s
         of NONE => raise Eval ("Arguments to + must be numbers", stk, env)
          | SOME ob => primAdd (ob :: stk, env))
  | primAdd (_ :: stk, env) = raise Eval ("Arguments to + must be numbers", stk, env)
  | primAdd (stk, env) = (stk, env)

fun primSub (INT x :: INT y :: stk, env) = (INT (y - x) :: stk, env)
  | primSub (INT x :: SYM s :: stk, env) =
      (case find env s
         of NONE => (INT (~ x) :: SYM s :: stk, env)
          | SOME ob => primSub (INT x :: ob :: stk, env))
  | primSub (INT x :: stk, env) = (INT (~ x) :: stk, env)
  | primSub (SYM s :: stk, env) =
      (case find env s
         of NONE => raise Eval ("Arguments to - must be numbers", stk, env)
          | SOME ob => primSub (ob :: stk, env))
  | primSub (t :: stk, env) = raise Eval ("Arguments to - must be numbers", t :: stk, env)
  | primSub (stk, env) = (stk, env)

fun primMul (INT x :: INT y :: stk, env) = (INT (y * x) :: stk, env)
  | primMul (INT x :: SYM s :: stk, env) =
      (case find env s
         of NONE => (INT x :: SYM s :: stk, env)
          | SOME ob => primMul (INT x :: ob :: stk, env))
  | primMul (INT x :: stk, env) = (INT x :: stk, env)
  | primMul (SYM s :: stk, env) =
      (case find env s
         of NONE => raise Eval ("Arguments to * must be numbers", stk, env)
          | SOME ob => primMul (ob :: stk, env))
  | primMul (_ :: stk, env) = raise Eval ("Arguments to * must be numbers", stk, env)
  | primMul (stk, env) = (stk, env)

fun primDiv (INT x :: INT y :: stk, env) = (INT (y div x) :: stk, env)
  | primDiv (INT x :: SYM s :: stk, env) =
      (case find env s
         of NONE => (INT (1 div x) :: stk, env)
          | SOME ob => primDiv (INT x :: ob :: stk, env))
  | primDiv (INT x :: stk, env) = (INT (1 div x) :: stk, env)
  | primDiv (SYM s :: stk, env) =
      (case find env s
         of NONE => raise Eval ("Arguments to / must be numbers", stk, env)
          | SOME ob => primDiv (ob :: stk, env))
  | primDiv (_ :: stk, env) = raise Eval ("Arguments to / must be numbers", stk, env)
  | primDiv (stk, env) = (stk, env)

fun primEq ([], env) = primEq ([NIL], env)
  | primEq (t :: [], env) = raise Eval ("Two arguments required for =", [t], env)
  | primEq (NIL :: NIL :: stk, env) = (BOOL true :: stk, env)
  | primEq (NIL :: SYM s :: stk, env) =
      (case find env s
         of NONE => raise Eval ("Undefined symbol " ^ s, stk, env)
          | SOME NIL => (BOOL true :: stk, env)
          | SOME _ => (BOOL false :: stk, env))
  | primEq (NIL :: stk, env) = (BOOL false :: stk, env)
  | primEq (INT x :: INT y :: stk, env) = (BOOL (x = y) :: stk, env)
  | primEq (INT x :: SYM s :: stk, env) =
      (case find env s
         of NONE => raise Eval ("Undefined symbol " ^ s, stk, env)
          | SOME ob => primEq (INT x :: ob :: stk, env))
  | primEq (INT x :: stk, env) = raise Eval ("Mismatched types for =", stk, env)
  | primEq (BOOL a :: BOOL b :: stk, env) = (BOOL (a = b) :: stk, env)
  | primEq (BOOL a :: SYM s :: stk, env) =
      (case find env s
         of NONE => raise Eval ("Undefined symbol " ^ s, stk, env)
          | SOME ob => primEq (BOOL a :: ob :: stk, env))
  | primEq (SYM s :: SYM t :: stk, env) =
      if s = t
      then (BOOL true :: stk, env)
      else (case find env s
              of NONE => raise Eval ("Undefined symbol " ^ s, stk, env)
               | SOME ob => primEq (ob :: SYM t :: stk, env))
  | primEq (QUEUE (headA, tailA) :: QUEUE (headB, tailB) :: stk, env) =
      let fun loop (NIL, NIL) = true
            | loop (NIL, _) = false
            | loop (_, NIL) = false
            | loop (QUEUE (ha, ta), QUEUE (hb, tb)) =
                (case primEq (ha :: hb :: stk, env)
                   of (BOOL true :: _, _) => true
                    | (BOOL false :: _, _) => false
                    | _ => false)
            | loop _ = false
      in case primEq (headA :: headB :: stk, env)
           of (BOOL true  :: _, _) => (BOOL (loop (tailA, tailB)) :: stk, env)
            | (BOOL false :: _, _) => (BOOL false :: stk, env)
            | _ => (BOOL false :: stk, env)
      end
  | primEq (QUEUE a :: NIL :: stk, env) = (BOOL false :: stk, env)
  | primEq (QUEUE a :: SYM s :: stk, env) =
      (case find env s
         of NONE => raise Eval ("Undefined symbol " ^ s, stk, env)
          | SOME ob => primEq (QUEUE a :: ob :: stk, env))
  | primEq (SYM s :: stk, env) =
      (case find env s
         of NONE => raise Eval ("Undefined symbol " ^ s, stk, env)
          | SOME ob => primEq (ob :: stk, env))
  | primEq (stk, env) = raise Eval ("Invalid type for =", stk, env)

fun primLambda (QUEUE body :: args :: stk, env) =
      let fun valid NIL = true
            | valid (QUEUE (SYM _, tail)) = valid tail
            | valid _ = false
      in if valid args
         then (CLOSURE (args, QUEUE body, env) :: stk, env)
         else raise Eval ("Arguments must be symbols", stk, env)
      end
  | primLambda (stk, env) = raise Eval ("Malformed lambda", stk, env)

fun primPrint ([], env) = primPrint ([NIL], env)
  | primPrint (SYM s :: stk, env) = (case find env s
                                      of SOME ob => primPrint (ob :: stk, env)
                                       | NONE => (print (repr (SYM s) ^ "\n");
                                                  (SYM s :: stk, env))
                                                  handle E err => raise Eval (err, SYM s :: stk, env))
  | primPrint (top :: stk, env) = (print (repr top ^ "\n");
                                   (top :: stk, env)
                                   handle E err => raise Eval (err, top :: stk, env))

fun primIf (_ :: t :: BOOL true :: stk, env) = eval t stk env
  | primIf (f :: _ :: BOOL false :: stk, env) = eval f stk env
  | primIf (_ :: _ :: INT _ :: stk, env) = raise Eval ("Malformed if", stk, env)
  | primIf (f :: t :: ob :: stk, env) = let val (stk', env') = eval ob stk env
                                        in primIf (f :: t :: stk', env)
                                        end
  | primIf (stk, env) = raise Eval ("Malformed if", stk, env)

fun primApply (QUEUE q :: stk, env) =
      (case apply (QUEUE q) [NIL] env
         of (result :: _, env') => (result :: stk, env')
          | (_, env') => (NIL :: stk, env'))
  | primApply (top :: stk, env) = apply top stk env
  | primApply ([], env) = primApply ([NIL], env)

fun debug (stk, env) =
  let fun printStack (top :: []) = repr top
        | printStack (top :: stk') = (repr top ^ " ") ^ printStack stk'
        | printStack [] = ""
      fun printEnv ((k, v) :: []) = "  '" ^ k ^ " : " ^ repr v
        | printEnv ((k, v) :: env') = "  '" ^ k ^ " : " ^ repr v ^ ",\n" ^ printEnv env'
        | printEnv [] = ""
  in (print ("{\n" ^ printEnv env ^ "\n}\n[" ^ printStack stk ^ "]\n");
      (stk, env))
  end

fun fileToQueue fname =
  let val stream = TextIO.openIn fname
      handle Io => raise E ("Error opening \"" ^ fname ^ "\"")
      fun loop NONE = NIL
        | loop (SOME (SYM "]")) = raise Syntax "Unexpected ]"
        | loop (SOME (SYM "}")) = raise Syntax "Unexpected ]"
        | loop (SOME ob) = QUEUE (ob, loop (read stream))
  in loop (read stream)
  end

fun prImport (SYM s :: stk, env) = (eval (fileToQueue s) stk env
                                    handle E err => raise Eval (err, SYM s :: stk, env))
  | prImport (stk, env) = raise Eval ("Invalid filename for import", stk, env)

fun primCar (QUEUE (head, tail) :: stk, env) = (head :: stk, env)
  | primCar (SYM s :: stk, env) = (case find env s
                                     of NONE => raise Eval ("Wrong type for head", stk, env)
                                      | SOME ob => primCar (ob :: stk, env))
  | primCar (stk, env) = raise Eval ("Wrong type for head", stk, env)

fun primCdr (QUEUE (head, tail) :: stk, env) = (tail :: stk, env)
  | primCdr (SYM s :: stk, env) = (case find env s
                                     of NONE => raise Eval ("Wrong type for head", stk, env)
                                      | SOME ob => primCdr (ob :: stk, env))
  | primCdr (stk, env) = raise Eval ("Wrong type for tail", stk, env)

fun primCons (tail :: head :: stk, env) = (QUEUE (head, tail) :: stk, env)
  | primCons (stk, env) = raise Eval ("Two arguments required for Q", stk, env)

fun primOr (BOOL a :: BOOL b :: stk, env) = (BOOL (a orelse b) :: stk, env)
  | primOr (stk, env) = raise Eval ("Two boolean arguments required for or", stk, env)

fun primAnd (BOOL a :: BOOL b :: stk, env) = (BOOL (a andalso b) :: stk, env)
  | primAnd (stk, env) = raise Eval ("Two boolean arguments required for and", stk, env)

fun primNot (BOOL b :: stk, env) = (BOOL (not b) :: stk, env)
  | primNot (stk, env) = raise Eval ("One boolean argument required for not", stk, env)

fun primLt (INT x :: INT y :: stk, env) = (BOOL (y < x) :: stk, env)
  | primLt (stk, env) = raise Eval ("Two numbers required for <", stk, env)

fun primGt (INT x :: INT y :: stk, env) = (BOOL (y > x) :: stk, env)
  | primGt (stk, env) = raise Eval ("Two numbers required for >", stk, env)

fun primLte (INT x :: INT y :: stk, env) = (BOOL (y <= x) :: stk, env)
  | primLte (stk, env) = raise Eval ("Two numbers required for <=", stk, env)

fun primGte (INT x :: INT y :: stk, env) = (BOOL (y >= x) :: stk, env)
  | primGte (stk, env) = raise Eval ("Two numbers required for >=", stk, env)

val basis = [ ("DEBUG",  PRIMITIVE debug),
              ("import", PRIMITIVE prImport),
              ("ifelse", PRIMITIVE primIf),
              ("apply",  PRIMITIVE primApply),
              ("print",  PRIMITIVE primPrint),
              ("MAKEFN", PRIMITIVE primLambda),
              ("def",    PRIMITIVE primDef),
              ("Q",      PRIMITIVE primCons),
              ("head",   PRIMITIVE primCar),
              ("tail",   PRIMITIVE primCdr),
              ("or",     PRIMITIVE primOr),
              ("and",    PRIMITIVE primAnd),
              ("not",    PRIMITIVE primNot),
              (">=",     PRIMITIVE primGte),
              ("<=",     PRIMITIVE primLte),
              (">",      PRIMITIVE primGt),
              ("<",      PRIMITIVE primLt),
              ("=",      PRIMITIVE primEq),
              ("/",      PRIMITIVE primDiv),
              ("*",      PRIMITIVE primMul),
              ("-",      PRIMITIVE primSub),
              ("+",      PRIMITIVE primAdd),
              ("true",   BOOL true),
              ("false",  BOOL false) ]

(*** Entry Point and REPL ***)

fun error (msg: string): unit = TextIO.output (TextIO.stdErr, (msg ^"\n"))

fun repl (s: Stack, e: Env): unit =
  case read TextIO.stdIn
    of NONE => ()
     | SOME (SYM "]") => raise Syntax "Unexpected ]"
     | SOME (SYM "}") => raise Syntax "Unexpected }"
     | SOME ob => let val (s', e') = eval ob s e
                  in case peek TextIO.stdIn
                       of NONE => repl (s', e')
                        | SOME c => if c = #"\n" orelse c = #";"
                                    then (print ("= " ^ repr (hd s') ^ "\n> ");
                                          repl (s', e'))
                                          handle E msg => raise Eval (msg, s', e')
                                    else repl (s', e')
                  end
  handle Syntax err => (error ("Syntax Error: " ^ err);
                        print "> ";
                        repl (s, e))
       | Eval (msg, stk, env) => (error ("Error: " ^ msg);
                                  print "> ";
                                  repl (stk, env))

fun runFile fname = (eval (fileToQueue fname) [NIL] basis; 0)
                    handle Abort code => code
                         | Syntax err => (error ("Syntax Error: "  ^ err); 1)
                         | Eval (msg, _, _) => (error ("Error: " ^ msg); 1)

fun main (exe: string, args: string list): int =
  case exe
    of "/usr/lib/smlnj/bin/sml" =>
      (case args
         of (_ :: fname :: _) => runFile fname
          | _ => (print "> "; repl ([NIL], basis); 0)
                 handle Abort code => code)
      | fname => runFile fname

fun test () = main ("/usr/lib/smlnj/bin/sml", [])
fun reload () = use "tbd.sml"

(*
val _ = main ("/usr/lib/smlnj/bin/sml", [])
*)
