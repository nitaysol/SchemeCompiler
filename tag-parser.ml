#use "reader.ml";;
open Reader

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)
let rec dup_exist = function
| [] -> false
| head::tail -> List.exists ((=) head) tail || dup_exist tail
let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  


let rec tag_parser_local input = match input with
  | Number(x) -> Const(Sexpr(Number(x)))
  | Bool(x) -> Const(Sexpr(Bool(x)))
  | Char(x) -> Const(Sexpr(Char(x)))
  | String(x) -> Const(Sexpr(String(x)))
  | TagRef(x) -> Const(Sexpr(TagRef(x)))
  | TaggedSexpr(x, rest) -> (match rest with
                            | Pair(Symbol("quote"),Pair(rest2,Nil)) ->   Const(Sexpr(TaggedSexpr (x, rest2)))
                            | _ -> Const(Sexpr (TaggedSexpr (x, rest))))
  | Pair(Symbol("quote"), Pair(x, Nil)) -> Const(Sexpr(x))
  | Symbol(x) -> if(List.mem x reserved_word_list) then raise X_syntax_error else Var(x)
  | Pair(Symbol("if"), x) -> if_parser x
  | Pair(Symbol("lambda"), x) -> lambda_parser x
  | Pair(Symbol("or"), x) -> or_parser x
  | Pair(Symbol("define"), x) -> define_parser x
  | Pair(Symbol("set!"), x) -> set_parser x
  | Pair(Symbol("begin"), x) -> seq_parser x
  | Pair(Symbol("and"), x) -> and_macro x
  | Pair(Symbol("let"), Pair(argsNDvals, body)) -> tag_parser_local (Pair(Pair(Symbol("lambda"), Pair(get_args argsNDvals, body)), get_vals argsNDvals))
  | Pair(Symbol("let*"), x) -> let_star_macro x
  | Pair(Symbol("letrec"), x) -> letrec_macro x
  | Pair(Symbol("quasiquote"), Pair(x, Nil)) -> tag_parser_local (quasi_macro x)
  | Pair(Symbol("cond"), x) -> tag_parser_local (cond_macro x)
  | Pair(x, y) -> Applic(tag_parser_local(x), list_of_exprs y)
  | _ -> raise X_syntax_error

and or_parser x = match x with
  | Nil -> Const(Sexpr(Bool(false)))
  | Pair(first, Nil) -> tag_parser_local first
  | Pair(first, rest) -> Or(list_of_exprs x)
  | _ -> raise X_syntax_error

and if_parser x = match x with
  | Pair(test, Pair(dit, Pair(dif,Nil))) -> If(tag_parser_local test, tag_parser_local dit, tag_parser_local dif)
  | Pair(test, Pair(dit, Nil)) -> If(tag_parser_local test, tag_parser_local dit, Const(Void))
  | _ -> raise X_syntax_error

and lambda_parser x = match x with
  | Pair(Symbol(s), body) -> LambdaOpt([], s, tag_parser_local (Pair(Symbol("begin"),body)))
  | Pair(args, body) -> if(body == Nil) then raise X_syntax_error else 
                        let args_list = args_to_list args in
                        if (dup_exist args_list) then raise X_syntax_error else
                        if (is_proper_list args) 
                        then LambdaSimple (args_list, tag_parser_local (Pair(Symbol("begin"), body)))
                        else LambdaOpt(List.rev(List.tl(List.rev args_list)), List.hd(List.rev args_list), tag_parser_local (Pair(Symbol("begin"),body)))
  | _ -> raise X_syntax_error

and is_proper_list x = match x with
  | Pair(x, y) -> is_proper_list y
  | Nil -> true
  | _ -> false

and args_to_list x = match x with
  | Pair(Symbol(s),rest) -> List.append [s] (args_to_list rest)
  | Symbol(s) -> [s]
  | Nil -> []
  | _ -> raise X_syntax_error

and list_of_exprs x = match x with
  | Nil -> []
  | Pair(first, Nil) -> [tag_parser_local first]
  | Pair(first, rest) -> List.append [tag_parser_local first] (list_of_exprs rest)
  | _ -> [tag_parser_local x]

and define_parser x = match x with
  | Pair(Pair(name, args_list), body) -> mit_define_macro x
  | Pair(name, Nil) -> let var_temp = tag_parser_local name in
                              if (is_var var_temp) then Def(var_temp, Const(Void)) else raise X_syntax_error
  | Pair(name, Pair(expr, Nil)) -> let var_temp = tag_parser_local name in
                                   if (is_var var_temp) then Def(var_temp, tag_parser_local expr) else raise X_syntax_error
  | _ -> raise X_syntax_error

and is_var x = match x with
  | Var(s) -> true
  | _ -> false

and set_parser x = match x with
  | Pair(name, Pair(expr, Nil)) -> let var_temp = tag_parser_local name in
                                  if (is_var var_temp) then Set(var_temp, tag_parser_local expr) else raise X_syntax_error
  | _ -> raise X_syntax_error

and seq_parser x = match x with
  | Nil -> Const(Void)
  | Pair(first, Nil) -> tag_parser_local first
  | Pair(first, rest) -> Seq(list_of_exprs x)
  | _ -> raise X_syntax_error

and and_macro x = match x with
  | Nil -> Const(Sexpr(Bool(true)))
  | Pair(first, rest) -> (let first_expr = tag_parser_local first in
                                          match rest with
                                          | Nil -> first_expr
                                          | rest -> If(first_expr, and_macro rest, Const(Sexpr(Bool(false)))))
  | _ -> raise X_syntax_error

and get_args x = match x with
  | Nil -> Nil
  | Pair(Pair(var, Pair(value, Nil)), Nil) -> Pair(var, Nil)
  | Pair(Pair(var, Pair(value, Nil)), nextVar) -> Pair(var, get_args nextVar)
  | _ -> raise X_syntax_error

and get_vals x = match x with
  | Nil -> Nil
  | Pair(Pair(var, Pair(value, Nil)), Nil) -> Pair(value, Nil)
  | Pair(Pair(var, Pair(value, Nil)), nextVar) -> Pair(value, get_vals nextVar)
  | _ -> raise X_syntax_error

and let_star_macro x = match x with
  | Pair(Nil, body) -> tag_parser_local (Pair(Symbol("let"), x))
  | Pair(Pair(Pair(var, Pair(value, Nil)), Nil), body) -> tag_parser_local (Pair(Symbol("let"), x))
  | Pair(Pair(Pair(var, Pair(value, Nil)), nextVar), body) -> tag_parser_local (Pair(Symbol("let"), Pair(Pair(Pair(var, Pair(value, Nil)), Nil), 
                                                                          Pair(Pair(Symbol("let*"), Pair(nextVar, body)), Nil))))
  | _ -> raise X_syntax_error

and letrec_macro x = match x with
  | Pair(Nil, body) -> tag_parser_local (Pair(Symbol("let"), x))
  | Pair(vars, body) -> tag_parser_local (Pair(Symbol("let"), Pair(whatever_vars vars, (make_sets vars body))))
  | _ -> raise X_syntax_error

  
and whatever_vars x = let whatever_sym = Pair(Symbol("quote"), Pair(Symbol("whatever"), Nil)) in
    match x with
  | Pair(Pair(var, Pair(value, Nil)), Nil) -> Pair(Pair(var, Pair(whatever_sym, Nil)), Nil)
  | Pair(Pair(var, Pair(value, Nil)), nextVar) -> Pair(Pair(var, Pair(whatever_sym, Nil)), whatever_vars nextVar)
  | _ -> raise X_syntax_error
  
and make_sets x y = match x with
  | Pair(Pair(var, Pair(value, Nil)), Nil) -> Pair(Pair(Symbol("set!"), Pair(var, Pair(value, Nil))), y)
  | Pair(Pair(var, Pair(value, Nil)), nextVar) -> Pair(Pair(Symbol("set!"), Pair(var, Pair(value, Nil))), (make_sets nextVar y))
  | _ -> raise X_syntax_error

and quasi_macro x = match x with
  | Pair(Symbol("unquote"), Pair(x, Nil)) -> x
  | Pair(Symbol("unquote-splicing"), x) -> raise X_syntax_error
  | Nil -> Pair(Symbol("quote"), Pair(Nil, Nil))
  | Symbol(s) -> Pair(Symbol("quote"), Pair(Symbol(s), Nil))
  | Pair(Pair(Symbol("unquote-splicing"), Pair(exp, Nil)), b) -> Pair(Symbol("append"), Pair(exp, Pair(quasi_macro b, Nil)))
  | Pair(a, Pair(Symbol("unquote-splicing"), Pair(exp, Nil))) -> Pair(Symbol("cons"), Pair(quasi_macro a, Pair(exp,Nil)))
  | Pair(a, b) -> Pair(Symbol("cons"), Pair(quasi_macro a, Pair(quasi_macro b, Nil)))
  | _ -> x

and mit_define_macro x = match x with
  | Pair(Pair(name, args_list), body) -> let lambda_value = Pair(Symbol("lambda"), Pair(args_list, body)) in
                                tag_parser_local (Pair(Symbol("define"), Pair(name, Pair(lambda_value, Nil))))
  | _ -> raise X_syntax_error

and cond_macro x = match x with
  | Pair(first_con, rest_con) -> (match first_con with
                                | Pair(Symbol("else"), y) -> (Pair(Symbol("begin"), y))
                                | Pair(condition, Pair(Symbol("=>"), body)) -> if (rest_con==Nil) then
                                                                              let f = Pair(Pair(Symbol("f"), Pair(Pair(Symbol("lambda"), Pair(Nil, Pair((Pair(Symbol("begin"), body)), Nil))), Nil)), Nil) in
                                                                              let value = Pair(Pair(Symbol("value"), Pair(condition, Nil)), f) in
                                                                              let new_body = Pair(Pair(Symbol("if"), Pair(Symbol("value"), Pair(Pair(Pair(Symbol("f"), Nil), Pair(Symbol("value"), Nil)), Nil))), Nil) in
                                                                              Pair(Symbol("let"), Pair(value, new_body))
                                                                              else
                                                                              let rest = Pair(Pair(Symbol("rest"), Pair(Pair(Symbol("lambda"), Pair(Nil, Pair(cond_macro rest_con, Nil))), Nil)), Nil) in
                                                                              let f = Pair(Pair(Symbol("f"), Pair(Pair(Symbol("lambda"), Pair(Nil, Pair((Pair(Symbol("begin"), body)), Nil))), Nil)), rest) in
                                                                              let value = Pair(Pair(Symbol("value"), Pair(condition, Nil)), f) in
                                                                              let new_body = Pair(Pair(Symbol("if"), Pair(Symbol("value"), Pair(Pair(Pair(Symbol("f"), Nil), Pair(Symbol("value"), Nil)), Pair(Pair(Symbol("rest"), Nil), Nil)))), Nil) in
                                                                              Pair(Symbol("let"), Pair(value, new_body))
                                                                               
                                | Pair(condition, body) -> if(rest_con == Nil) then Pair(Symbol("if"), Pair(condition, Pair((Pair(Symbol("begin"), body)), Nil)))
                                                           else Pair(Symbol("if"), Pair(condition, Pair((Pair(Symbol("begin"), body)) , Pair((cond_macro rest_con), Nil))))
                                | _ -> raise X_syntax_error)
  | Nil -> Nil
  | _ -> raise X_syntax_error;;

let tag_parse_expression sexpr = tag_parser_local sexpr;;


let tag_parse_expressions sexpr = List.map tag_parser_local sexpr;;

end;; (* struct Tag_Parser *)
 
