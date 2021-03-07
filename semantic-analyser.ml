#use "tag-parser.ml";;
open Tag_Parser;;
type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

  (* ###############START############# *)
  (* Lexical Annotation *)
let rec lex_annotate paramsEnv boundsEnv expr = 
  let lex_annotateS e = lex_annotate paramsEnv boundsEnv e in
  match expr with
  | Const(x) -> Const'(x)
  | Var(x) -> (let isVarInParams = find_x_in_list x paramsEnv 0 in
                if (isVarInParams != -1) then Var'(VarParam(x, isVarInParams))
                else varHandler x boundsEnv 0)
  | If(test, dit, dif) -> If'(lex_annotateS test, lex_annotateS dit, lex_annotateS dif) 
  | Seq(lst) -> Seq'(List.map (lex_annotateS) lst)
  | Set(var, value) -> Set'(lex_annotateS var, lex_annotateS value)
  | Def(var, value) -> Def'(lex_annotateS var, lex_annotateS value)
  | Or(lst) -> Or'(List.map (lex_annotateS) lst)
  | LambdaSimple(params, body) -> LambdaSimple'(params, lex_annotate params (List.append [paramsEnv] boundsEnv) body)
  | LambdaOpt(params, opt, body) -> LambdaOpt'(params, opt, lex_annotate (List.append params [opt]) (List.append [paramsEnv] boundsEnv) body)
  | Applic(f, args_lst) -> Applic'(lex_annotateS f, List.map (lex_annotateS) args_lst)

and varHandler var boundsEnv b_counter = match boundsEnv with
  | [] -> Var'(VarFree(var))
  | h :: t -> let isVarInEnv = find_x_in_list var h 0 in
              if (isVarInEnv != -1) then Var'(VarBound(var, b_counter, isVarInEnv))
              else varHandler var t (1 + b_counter)
(* /Lexical Annotation *)

(* Tails Annotation *)
and tl_annotate in_tp expr = 
let tl_annotateSfalse e = tl_annotate false e in
let tl_annotateStrue e = tl_annotate true e in
match expr with
| Const'(x) -> Const'(x)
| Var'(x) -> Var'(x)
| If'(test, dit, dif) -> If'(tl_annotateSfalse test, tl_annotate in_tp dit, tl_annotate in_tp dif)
| Seq'(lst) -> Seq'(handleSequences in_tp lst)
| Set'(var, value) -> Set'(tl_annotateSfalse var, tl_annotateSfalse value)
| Def'(var, value) -> Def'(tl_annotateSfalse var , tl_annotateSfalse value )
| Or'(lst) -> Or'(handleSequences in_tp lst)
| LambdaSimple'(params, body) -> LambdaSimple'(params, tl_annotateStrue body)
| LambdaOpt'(params, opt, body) -> LambdaOpt'(params, opt, tl_annotateStrue body)
| Applic'(f, args_lst) -> if (in_tp) then ApplicTP'(tl_annotateSfalse f, List.map (tl_annotateSfalse) args_lst)
                          else Applic'(tl_annotateSfalse f, List.map (tl_annotateSfalse) args_lst)
| _ -> raise X_syntax_error


and handleSequences in_tp expr_lst = match expr_lst with
| [] -> []
| h :: [] -> [tl_annotate in_tp h]
| h :: t ->  List.append [tl_annotate false h] (handleSequences in_tp t)


(* /Tails Annotation *)

(* Boxing handling *)
and readAndWrite param r_Or_w currentExpr = 
let readAndWriteS e = readAndWrite param r_Or_w e in
match currentExpr with
| Const'(x) -> false
| Var'(x) -> if (r_Or_w = 0 && (getVarsString x) = param) then true else false
| If'(test, dit, dif) -> readAndWriteS test || readAndWriteS dit || readAndWriteS dif
| Seq'(lst) -> List.fold_right (fun a b -> (readAndWriteS a) || b) lst false
| Set'(Var'(var), value) -> if (r_Or_w = 1 && (getVarsString var) = param) then true else (readAndWriteS value)
| Def'(var, value) -> readAndWriteS value
| Or'(lst) -> List.fold_right (fun a b -> (readAndWriteS a) || b) lst false
| LambdaSimple'(params, body) -> if (not (List.mem param params)) then readAndWriteS body else false
| LambdaOpt'(params, opt, body) -> if (not (List.mem param (List.append params [opt]))) then readAndWriteS body else false
| Applic'(f, args_lst) -> (readAndWriteS f) || (List.fold_right (fun a b -> (readAndWriteS a) || b) args_lst false)
| ApplicTP'(f, args_lst) -> (readAndWriteS f) || (List.fold_right (fun a b -> (readAndWriteS a) || b) args_lst false)
| _ -> false

and readAndWriteFromBody param r_Or_w currentExpr = 
let readAndWriteS e = readAndWriteFromBody param r_Or_w e in
match currentExpr with
| Const'(x) -> false
| Var'(x) -> if (r_Or_w = 0 && (getVarsString x) = param) then true else false
| If'(test, dit, dif) -> readAndWriteS test || readAndWriteS dit || readAndWriteS dif
| Seq'(lst) -> List.fold_right (fun a b -> (readAndWriteS a) || b) lst false
| Set'(Var'(var), value) -> if (r_Or_w = 1 && (getVarsString var) = param) then true else (readAndWriteS value)
| Def'(var, value) -> readAndWriteS value
| Or'(lst) -> List.fold_right (fun a b -> (readAndWriteS a) || b) lst false
| LambdaSimple'(params, body) -> false
| LambdaOpt'(params, opt, body) -> false
| Applic'(f, args_lst) -> (readAndWriteS f) || (List.fold_right (fun a b -> (readAndWriteS a) || b) args_lst false)
| ApplicTP'(f, args_lst) -> (readAndWriteS f) || (List.fold_right (fun a b -> (readAndWriteS a) || b) args_lst false)
| _ -> false

and get_Lambda_list expr = 
  match expr with
  | Const'(x) -> []
  | Var'(x) -> []
  | If'(test, dit, dif) -> (List.append (get_Lambda_list test) (List.append (get_Lambda_list dit) (get_Lambda_list dif)))
  | Seq'(lst) -> List.fold_right (fun a b -> List.append a b) (List.map get_Lambda_list lst) []
  | Set'(var, value) -> get_Lambda_list value
  | Def'(var, value) -> get_Lambda_list value
  | Or'(lst) -> List.fold_right (fun a b -> List.append a b) (List.map get_Lambda_list lst) []
  | LambdaSimple'(params, body) -> [expr]
  | LambdaOpt'(params, opt, body) -> [expr]
  | Applic'(f, args_lst) -> List.append (get_Lambda_list f) (List.fold_right (fun a b -> List.append a b) (List.map get_Lambda_list args_lst) [])
  | ApplicTP'(f, args_lst) -> List.append (get_Lambda_list f) (List.fold_right (fun a b -> List.append a b) (List.map get_Lambda_list args_lst) [])
  | _ -> []

and should_box_param body param = let lambdasList = get_Lambda_list body in
let lambdas_results = List.append [((readAndWriteFromBody param 0 body),(readAndWriteFromBody param 1 body))] (List.map (fun x -> ((readAndWrite param 0 x),(readAndWrite param 1 x))) lambdasList) in
let lambdas_results = List.mapi (fun i x -> (i, x)) lambdas_results in
let readers = List.map (fun (i, (read, write)) -> i) (List.filter (fun (i, (read, write)) -> read) lambdas_results) in
let writers = List.map (fun (i, (read, write)) -> i) (List.filter (fun (i, (read, write)) -> write) lambdas_results) in
match readers with
| [] -> false
| h::t -> match writers with
        | [] -> false
        | h2::t2 -> if (List.length readers = 1 && List.length writers == 1) then (List.hd readers) != (List.hd writers) else true


and should_box_params_list params body varsNeededToBeBoxed = 
  let remove_params_from_VarsNeededToBeBoxed = lst_diff varsNeededToBeBoxed params in
  let add_params_needed_to_be_boxed = List.append remove_params_from_VarsNeededToBeBoxed (List.filter (should_box_param body) params) in
  let updatedvarsNeededToBeBoxed = add_params_needed_to_be_boxed in
  let intersectionList = List.rev (intersection updatedvarsNeededToBeBoxed params) in
  match intersectionList with
  | [] -> handleBoxing updatedvarsNeededToBeBoxed body
  | h::t -> let new_body = Seq'(List.append (List.map (fun(x) -> let var_x = VarParam(x, find_x_in_list x params 0) in
                                                      Set'(Var'(var_x),Box'(var_x))) intersectionList)[handleBoxing updatedvarsNeededToBeBoxed body]) in
           new_body

and handleBoxing varsNeededToBeBoxed expr = 
  let handleBoxingS e = handleBoxing varsNeededToBeBoxed e in
  match expr with
  | Const'(x) -> Const'(x)
  | Var'(x) -> if (List.mem (getVarsString x) varsNeededToBeBoxed) then BoxGet'(x) else Var'(x)
  | If'(test, dit, dif) -> If'(handleBoxingS test, handleBoxingS dit, handleBoxingS dif)
  | Seq'(lst) -> Seq'(List.map handleBoxingS lst)
  | Set'(Var'(var), value) -> let value_after_checking = handleBoxingS value in 
                                           if (List.mem (getVarsString var) varsNeededToBeBoxed) then BoxSet'(var, value_after_checking)
                                           else Set'(Var'(var), value_after_checking)
  | Def'(var, value) -> Def'(handleBoxingS var, handleBoxingS value)
  | Or'(lst) -> Or'(List.map handleBoxingS lst)
  | LambdaSimple'(params, body) -> let new_body = (should_box_params_list params body varsNeededToBeBoxed) in
                                  LambdaSimple'(params, new_body)
  | LambdaOpt'(params, opt, body) -> let new_body = (should_box_params_list (List.append params [opt]) body varsNeededToBeBoxed) in
                                LambdaOpt'(params, opt,  new_body)
  | Applic'(f, args_lst) -> Applic'(handleBoxingS f, List.map handleBoxingS args_lst)
  | ApplicTP'(f, args_lst) -> ApplicTP'(handleBoxingS f, List.map handleBoxingS args_lst)
  | x -> x

and getVarsString var = match var with
  | VarFree(x) -> x
  | VarParam(x,y) -> x
  | VarBound(x,y,z) -> x  

(* /Boxing handling *)
(* Helping funcs *)
and find_x_in_list x lst counter = match lst with
  | [] -> -1
  | h :: t -> if x = h then counter else find_x_in_list x t (counter+1)

and lst_diff l1 l2 = List.filter (fun x -> not (List.mem x l2)) l1
and intersection l1 l2 = List.fold_left (fun acc x -> if(List.exists (fun y -> y=x) l1) then x::acc else acc) [] l2;;
(* /Helping funcs *)
(* #############END############ *)
let annotate_lexical_addresses e = lex_annotate [] [] e;;

let annotate_tail_calls e = tl_annotate false e;;

let box_set e = handleBoxing [] e;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)


