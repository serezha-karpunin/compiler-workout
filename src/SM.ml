open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config


let eval_insn config insn = 
	let (stack, stmt_config) = config in
	let (state, input, output) = stmt_config in
	match insn with
	| BINOP operator -> (match stack with
		| y::x::tail -> ([(Language.Expr.get_operator operator) x y]@tail, stmt_config))
	| CONST value -> ([value]@stack, stmt_config)                 
	| READ -> (match input with
		| head::tail -> ([head]@stack, (state, tail, output)))
	| WRITE -> (match stack with
		| head::tail -> (tail, (state, input, output@[head])))
	| LD  variable_name -> ([state variable_name]@stack, stmt_config)
	| ST  variable_name -> (match stack with
		| head::tail -> (tail, (Language.Expr.update variable_name head state, input, output)))

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let eval config prg = List.fold_left eval_insn config prg

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Language.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compile_expr expr = 
	match expr with
		| Language.Expr.Const const -> [CONST const]
        | Language.Expr.Var var -> [LD var]
        | Language.Expr.Binop (operator, left_expression, right_expression) -> (compile_expr left_expression)@(compile_expr right_expression)@[BINOP operator];;

let rec compile statement = 
	match statement with
		| Language.Stmt.Read variable_name -> [READ; ST variable_name]
		| Language.Stmt.Write expression -> (compile_expr expression)@[WRITE]
		| Language.Stmt.Assign (variable_name, expression) -> (compile_expr expression)@[ST variable_name]
		| Language.Stmt.Seq (statement1, statement2) -> (compile statement1)@(compile statement2);;
