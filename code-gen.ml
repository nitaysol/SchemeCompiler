#use "semantic-analyser.ml";;
(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "SOB_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* This signature represents the idea of outputing assembly code as a string
     for a single AST', given the full constants and fvars tables. 
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;




(* ----------------------------------------------------------------------------------------------------------------------------- *)

(* GLOBALS *)
let ast_index = ref 1;;
let count_Lexit = ref 0;;
let count_Lelse = ref 0;;
let count_Lcode = ref 0;;
let count_Lcont = ref 0;;
let count_LambdaOpt = ref 0;;
(* \GLOBALS *)


let fvars_init = ["boolean?"; "float?" ; "integer?"; "pair?"; "null?"; "char?"; "string?"; "procedure?" ; "symbol?"; "string-length"; "string-ref"; "string-set!";
"make-string"; "symbol->string"; "char->integer"; "integer->char"; "eq?"; "+"; "*"; "-"; "/"; "<"; "="; "car"; "cdr"; "set-car!"; "set-cdr!"; "cons"; "apply"];;

(*       make_fvars_tbl        *)
let rec make_fvars_tbl_local asts = let free_vars_lst = List.fold_right (fun a b -> List.append a b) (List.map take_all_free_vars asts) [] in
let free_vars_lst = remove_dup (fvars_init @ free_vars_lst) in
let free_vars_lst = List.mapi (fun i x -> (x, i)) free_vars_lst in
free_vars_lst

and get_fvar_index fvars_lst fvar = match fvars_lst with
  | [] -> -1
  | (h_name, h_index)::t -> if (fvar = h_name) then h_index else get_fvar_index t fvar

and take_all_free_vars ast = match ast with
  | Const'(x) -> []
  | Var'(VarFree(x)) -> [x]
  | If'(test, dit, dif) -> (List.append (take_all_free_vars test) (List.append (take_all_free_vars dit) (take_all_free_vars dif)))
  | Seq'(lst) -> List.fold_right (fun a b -> List.append a b) (List.map take_all_free_vars lst) []
  | Set'(var, value) -> List.append (take_all_free_vars var) (take_all_free_vars value)
  | BoxSet'(name, expr) -> take_all_free_vars expr
  | Def'(var, value) -> List.append (take_all_free_vars var) (take_all_free_vars value)
  | Or'(lst) -> List.fold_right (fun a b -> List.append a b) (List.map take_all_free_vars lst) []
  | LambdaSimple'(params, body) -> take_all_free_vars body
  | LambdaOpt'(params, opt, body) -> take_all_free_vars body
  | Applic'(f, args_lst) -> List.append (take_all_free_vars f) (List.fold_right (fun a b -> List.append a b) (List.map take_all_free_vars args_lst) [])
  | ApplicTP'(f, args_lst) -> List.append (take_all_free_vars f) (List.fold_right (fun a b -> List.append a b) (List.map take_all_free_vars args_lst) [])
  | _ -> []
(*       /make_fvars_tbl        *)


and remove_dup lst = match lst with
  | [] -> []
  | h::[] -> h::[]
  | h::t -> if (List.mem h t) then (remove_dup t) else (List.append [h] (remove_dup t))


(*       make_consts_tbl        *)


and rename_tag_expressions index ast = let rename_shortcut ast = (rename_tag_expressions index) ast in
let const_handle sexpr = const_removal (rename_shortcut (Const'(Sexpr(sexpr)))) in
match ast with
  | Const'(Sexpr(TaggedSexpr(name, value))) -> Const'(Sexpr(TaggedSexpr(name^index, const_handle value)))
  | Const'(Sexpr(TagRef(name))) -> Const'(Sexpr(TagRef(name^index)))
  | Const'(Sexpr(Pair(first,rest))) -> Const'(Sexpr(Pair(const_handle first, const_handle rest)))
  | If'(test, dit, dif) -> If'(rename_shortcut test, rename_shortcut dit, rename_shortcut dif)
  | Seq'(lst) -> Seq'(List.map rename_shortcut lst)
  | Set'(var, value) -> Set'(var, rename_shortcut value)
  | BoxSet'(name, expr)-> BoxSet'(name, rename_shortcut expr)
  | Def'(var, value) -> Def'(var, rename_shortcut value)
  | Or'(lst) -> Or'(List.map rename_shortcut lst)
  | LambdaSimple'(params, body) -> LambdaSimple'(params, rename_shortcut body)
  | LambdaOpt'(params, opt, body) -> LambdaOpt'(params, opt, rename_shortcut body)
  | Applic'(f, args_lst) -> Applic'(rename_shortcut f, List.map rename_shortcut args_lst)
  | ApplicTP'(f, args_lst) -> ApplicTP'(rename_shortcut f, List.map rename_shortcut args_lst)
  | _ -> ast

and contains_Sexpr sexprLst sexpr = match sexprLst with
  | [] -> false
  | h :: t ->  if(sexpr_eq h sexpr) then true else (contains_Sexpr t sexpr)


and contains_Sexpr_tuple tupleLst sexpr = match tupleLst with
  | [] -> -1
  | h :: t -> (match h with
              | (Sexpr(expr), (off_set, code)) -> if (sexpr_eq sexpr expr) then off_set else contains_Sexpr_tuple t sexpr
              | _ -> contains_Sexpr_tuple t sexpr)

and remove_dup_sexpr lst = match lst with
  | [] -> []
  | h::[] -> h::[]
  | h::t -> if (contains_Sexpr t h) then (remove_dup_sexpr t) else (List.append [h] (remove_dup_sexpr t))

and separteTagSexpr sexprLst tag_lst sexpr_lst_updated = match sexprLst with
 | [] -> (tag_lst,sexpr_lst_updated)
 | h::t -> (match h with
          | TaggedSexpr(name, value) -> separteTagSexpr t (tag_lst @ [(name, remove_Tagged_in_Sexpr value)]) sexpr_lst_updated
          | _ -> separteTagSexpr t tag_lst (sexpr_lst_updated @ [h]))

and remove_Tagged_in_Sexpr sexpr = match sexpr with
| TaggedSexpr(name, value) -> remove_Tagged_in_Sexpr value
| Pair(a, b) -> Pair(remove_Tagged_in_Sexpr a, remove_Tagged_in_Sexpr b)
| _ -> sexpr

and collect_all_sexpr ast = match ast with
  | Const'(x) -> (match x with
                | Sexpr(y) -> (match y with
                              | Symbol(s) ->  [String(s); y]
                              | Pair(a, b) -> (let car_cdr = ((collect_all_sexpr (Const'(Sexpr a))) @ (collect_all_sexpr (Const'(Sexpr b)))) in
                                              car_cdr @ [(remove_Tagged_in_Sexpr (Pair(a, b)))])
                              | TaggedSexpr(name, value) -> [y] @ (collect_all_sexpr (Const'(Sexpr value)))
                              | Nil -> []
                              | Bool(z) -> []
                              | _ -> [y]
                              )
                | _ -> [])
  | If'(test, dit, dif) -> (collect_all_sexpr test) @ (collect_all_sexpr dit) @ (collect_all_sexpr dif)
  | Seq'(lst) -> List.fold_right (fun a b -> List.append a b) (List.map collect_all_sexpr lst) []
  | Set'(var, value) -> List.append (collect_all_sexpr var) (collect_all_sexpr value)
  | Def'(var, value) -> List.append (collect_all_sexpr var) (collect_all_sexpr value)
  | Or'(lst) -> List.fold_right (fun a b -> List.append a b) (List.map collect_all_sexpr lst) []
  | BoxSet'(name, expr)-> collect_all_sexpr expr
  | LambdaSimple'(params, body) -> collect_all_sexpr body
  | LambdaOpt'(params, opt, body) -> collect_all_sexpr body
  | Applic'(f, args_lst) -> List.append (collect_all_sexpr f) (List.fold_right (fun a b -> List.append a b) (List.map collect_all_sexpr args_lst) [])
  | ApplicTP'(f, args_lst) -> List.append (collect_all_sexpr f) (List.fold_right (fun a b -> List.append a b) (List.map collect_all_sexpr args_lst) [])
  | _ -> []
            
and make_consts_tbl_local asts = let asts_after_renaming = List.mapi (fun i x -> rename_tag_expressions (string_of_int (i+1)) x) asts in
  let sexprLst = (List.fold_right (fun a b -> List.append a b) (List.map (collect_all_sexpr) asts_after_renaming) []) in
  let sexprLst = List.rev (remove_dup_sexpr (List.rev sexprLst)) in
  let (tag_lst, sexprLst) = separteTagSexpr sexprLst [] [] in
  let constant_table = sexpr_to_tuple 6 (sexprLst) [(Sexpr(Nil), (1, "MAKE_NIL"));
  (Sexpr(Bool false), (2, "MAKE_BOOL(0)"));
  (Sexpr(Bool true), (4, "MAKE_BOOL(1)"))] tag_lst in
  let constant_table = update_tag_refs constant_table tag_lst constant_table in
  let constant_table = [(Void, (0, "MAKE_VOID"))] @ constant_table in
  constant_table


and tag_name_to_value name tag_lst = match tag_lst with
  | [] -> raise X_syntax_error
  | (h_name, h_value)::t -> if (h_name = name) then h_value else tag_name_to_value name t
  
and sexpr_to_tuple off_set sexprlst tuple_lst tag_lst = match sexprlst with
  | [] -> tuple_lst
  | h::t -> ( let new_off_set = off_set + (get_size_to_add h) in
              let sexpr = Sexpr(h) in
              let continuation = (match h with
              | Char(c) -> [(sexpr, (off_set, "MAKE_LITERAL_CHAR(" ^ (string_of_int (int_of_char c)) ^ ")"))]
              | String(s) -> (match s with
                            | "" -> [(sexpr, (off_set, "MAKE_LITERAL_STRING \"" ^ s ^ "\""))]
                            | _ -> [(sexpr, (off_set, "MAKE_LITERAL_STRING " ^ List.fold_left (fun a b -> a ^ b) "" (List.map (fun a -> (string_of_int a)^",") (List. map Char.code (string_to_list s)))))])
              | Symbol(s) -> [(sexpr, (off_set, "MAKE_LITERAL_SYMBOL(const_tbl+" ^ (string_of_int (contains_Sexpr_tuple tuple_lst (String (s)))) ^ ")" ))]
              | Number(Int(x)) -> [(sexpr,(off_set, "MAKE_LITERAL_INT("^(string_of_int x)^")"))]
              | Number(Float(x)) -> [(sexpr,(off_set, "MAKE_LITERAL_FLOAT("^(string_of_float x)^")"))]
              | Pair(a, b) -> [(sexpr,(off_set, "MAKE_LITERAL_PAIR(const_tbl+"^ (string_of_int (contains_Sexpr_tuple tuple_lst a)) ^ ", const_tbl+"^ (string_of_int (contains_Sexpr_tuple tuple_lst b)) ^" )"))]
              | _ -> []) in
              sexpr_to_tuple new_off_set t (tuple_lst @ continuation) tag_lst
  )

and update_tag_refs tuple_lst tag_lst tuple_lst_full = match tuple_lst with
  | [] -> []
  | (sexpr, (off_set, code))::t -> let update = (match sexpr with
            | (Sexpr(Pair(TagRef(car), TagRef(cdr)))) -> let a = tag_name_to_value car tag_lst in
                                                         let b = tag_name_to_value cdr tag_lst in
                                                         [(sexpr,(off_set, "MAKE_LITERAL_PAIR(const_tbl+"^ (string_of_int (contains_Sexpr_tuple tuple_lst_full a)) ^ ", const_tbl+"^ (string_of_int (contains_Sexpr_tuple tuple_lst_full b)) ^" )"))]
            | (Sexpr(Pair(TagRef(car), b))) -> let a = tag_name_to_value car tag_lst in
                                               [(sexpr,(off_set, "MAKE_LITERAL_PAIR(const_tbl+"^ (string_of_int (contains_Sexpr_tuple tuple_lst_full a)) ^ ", const_tbl+"^ (string_of_int (contains_Sexpr_tuple tuple_lst_full b)) ^" )"))]
            | (Sexpr(Pair(a, TagRef(cdr)))) -> let b =  tag_name_to_value cdr tag_lst in
                                               [(sexpr,(off_set, "MAKE_LITERAL_PAIR(const_tbl+"^ (string_of_int (contains_Sexpr_tuple tuple_lst_full a)) ^ ", const_tbl+"^ (string_of_int (contains_Sexpr_tuple tuple_lst_full b)) ^" )"))]
            | _ -> [(sexpr, (off_set, code))]
            ) in
            update @ (update_tag_refs t tag_lst tuple_lst_full)
  
and get_size_to_add sexpr = match sexpr with
  | Number(Int(x)) -> 9
  | Number(Float(x)) -> 9
  | String(s) -> 9 + (String.length s)
  | Char(c) -> 2
  | Symbol(s) -> 9
  | Pair(a, b) -> 17
  | _ -> 0

and const_removal x = match x with
  | Const'(Sexpr(y)) -> y
  | _ -> raise X_this_should_not_happen

(*       /make_consts_tbl        *)



(*       generate_code        *)
and generate_local lambda_counter consts fvars e = 
  match e with
  | Const'(c) -> (match c with
                | Sexpr(s) -> "mov rax, const_tbl+"^ (string_of_int (contains_Sexpr_tuple consts (remove_Tagged_in_Sexpr s)) ^"\n")
                | _ -> "mov rax, const_tbl\n")
  | Var'(var) -> (match var with
                  | VarParam(_, minor) -> "mov rax, qword [rbp + WORD_SIZE * (4 +" ^ (string_of_int minor) ^ ")]\n"
                  | VarBound(_, major, minor) -> "mov rax, qword [rbp + (2 * WORD_SIZE)]
                                                  mov rax, qword [rax + WORD_SIZE *" ^ (string_of_int major) ^ "]
                                                  mov rax, qword [rax + WORD_SIZE *" ^ (string_of_int minor) ^ "]\n"
                  | VarFree(v) -> "mov rax, qword [fvar_tbl + " ^ (string_of_int (get_fvar_index fvars v)) ^ " * WORD_SIZE]\n")
  | Set'(Var'(var), value) -> let value_str = (generate_local lambda_counter consts fvars value) in
                        (match var with
                         | VarParam(_, minor) -> value_str ^ "mov qword [rbp + (4 +" ^ (string_of_int minor) ^ ") * WORD_SIZE], rax\n
                                                              mov rax, SOB_VOID_ADDRESS\n"
                         | VarBound(_, major, minor) -> value_str ^ "mov rbx, qword [rbp + (2 * WORD_SIZE)]
                                                                     mov rbx, qword [rbx + (" ^ (string_of_int major) ^ " * WORD_SIZE)]
                                                                     mov qword [rbx + (" ^ (string_of_int minor) ^ ") * WORD_SIZE], rax
                                                                     mov rax, SOB_VOID_ADDRESS\n"
                         | VarFree(v) -> value_str ^ "mov qword [fvar_tbl + " ^ (string_of_int (get_fvar_index fvars v)) ^ " * WORD_SIZE], rax
                                                      mov rax, SOB_VOID_ADDRESS\n"
                        )
  | Seq'(lst) -> List.fold_right (fun a b -> a ^ b) (List.map (generate_local lambda_counter consts fvars) lst) ""
  | Or'(lst) -> ignore(count_Lexit := !count_Lexit + 1);
                let counter = (string_of_int !count_Lexit) in
                (List.fold_right (fun a b -> a ^ b) (List.map (fun a -> (generate_local lambda_counter consts fvars a) ^ "cmp rax, SOB_FALSE_ADDRESS \n jne Lexit" ^ counter ^ "\n") lst) "")
                ^ "Lexit" ^ counter ^ ":\n"
  | If'(test, dit, dif) -> ignore(count_Lelse := !count_Lelse + 1);
                           ignore(count_Lexit := !count_Lexit + 1);
                           let lexit_counter = "Lexit" ^ (string_of_int !count_Lexit) in
                           let else_counter = "Lelse" ^ (string_of_int !count_Lelse) in
                           let test_value = (generate_local lambda_counter consts fvars test) in
                           let dit_value = (generate_local lambda_counter consts fvars dit) in
                           let dif_value = (generate_local lambda_counter consts fvars dif) in
                           test_value ^ "cmp rax, SOB_FALSE_ADDRESS \n je " ^ else_counter ^ "\n" ^ dit_value ^ "jmp " ^ lexit_counter ^ "\n" ^
                           else_counter ^ ":\n " ^ dif_value ^ lexit_counter ^ ":\n"
  | BoxGet'(v) -> let var_value = (generate_local lambda_counter consts fvars (Var'(v))) in var_value ^ "mov rax, qword [rax]\n"
  | BoxSet'(v, value) -> let value = (generate_local lambda_counter consts fvars value) in
                         let var_value = (generate_local lambda_counter consts fvars (Var'(v))) in
                         value ^ "push rax\n" ^ var_value ^ "pop qword [rax] \n mov rax, SOB_VOID_ADDRESS\n"
  | Box'(v) -> let var_value = (generate_local lambda_counter consts fvars (Var'(v))) in
               var_value ^ "MALLOC rbx, WORD_SIZE \n mov qword [rbx], rax\n mov rax, rbx\n"
  | Def'(Var'(VarFree(name)), value) -> let value_local = generate_local lambda_counter consts fvars value in
                        value_local ^ "mov qword [fvar_tbl + " ^ (string_of_int (get_fvar_index fvars name)) ^ " * WORD_SIZE], rax
                        mov rax, SOB_VOID_ADDRESS\n"
  | LambdaSimple'(params, body) -> generate_lambda 0 lambda_counter consts fvars params body
  | LambdaOpt'(params,opt, body) -> generate_lambda 1 lambda_counter consts fvars (params @ [opt]) body
  | Applic'(f, args) -> let args_f_eval = (applic_generator f args lambda_counter consts fvars) in
                        let call_closure = "cmp byte [rax], T_CLOSURE \n jne OMG_ERROR_OMG \n push qword [rax + 1] \n call [rax + 1 + WORD_SIZE]\n" in
                        let clean_stack = "add rsp, WORD_SIZE \n pop rbx \n inc rbx \n shl rbx, 3 \n add rsp, rbx\n" in
                        args_f_eval ^ call_closure ^ clean_stack
  | ApplicTP'(f, args) -> let args_f_eval = (applic_generator f args lambda_counter consts fvars) in
                          let before_shift = "cmp byte [rax], T_CLOSURE \n jne OMG_ERROR_OMG \n push qword [rax + 1] \n push qword [rbp + 8 * 1]\n push qword [rbp]\n" in
                          let shift_and_jmp_closure = "mov rbx, PARAM_COUNT \n SHIFT_FRAME (5 + " ^ (string_of_int (List.length args)) ^ ") \n add rbx, 5 \n shl rbx, 3 \n add rsp, rbx
                          pop rbp \n jmp [rax + 1 + WORD_SIZE]\n" in
                          args_f_eval ^ before_shift ^ shift_and_jmp_closure
                          
  | _ -> "______ERROR_______"

and applic_generator f args lambda_counter consts fvars = let args_eval_lst = List.map (fun a -> (generate_local lambda_counter consts fvars a) ^ "push rax\n") args in
                              let magic_number = "push SOB_NIL_ADDRESS\n" in
                              let args_eval = magic_number ^ ((List.fold_right (fun a b -> a ^ b) (List.rev args_eval_lst) "") ^ "push " ^ (string_of_int (List.length args)) ^ "\n") in
                              let f_eval = (generate_local lambda_counter consts fvars f) in
                              args_eval ^ f_eval
(*       /generate_code        *)
(* ----------------------------------------------------------------------------------------------------------------------------- *)
and generate_lambda simple_or_opt lambda_counter consts fvars params body = 
    ignore(count_Lcont := !count_Lcont + 1);
    ignore(count_Lcode := !count_Lcode + 1);
    ignore(count_LambdaOpt := !count_LambdaOpt + 1);
    let lcode_counter = "Lcode" ^ (string_of_int !count_Lcode) in
    let lcont_counter = "Lcont" ^ (string_of_int !count_Lcont) in
    let lambdaOpt_counter = (string_of_int !count_LambdaOpt) in
    let body_str = (generate_local (lambda_counter+1) consts fvars body) in
    let allocate_ext_env = "MALLOC r10, WORD_SIZE * " ^ (string_of_int (lambda_counter)) ^ "\n" in
    let lex_env = "mov rsi, qword [rbp + 2 * WORD_SIZE]\n" in
    let copy_minor_envs = " mov rcx, " ^ (string_of_int (lambda_counter-1)) ^ " \n mov rdi, r10 \n add rdi, WORD_SIZE
    rep movsq
    " in
    let param_env_malloc = "mov rcx, PARAM_COUNT
    inc rcx
    shl rcx, 3
    MALLOC rdx, rcx
    mov rdi, rdx
    shr rcx, 3
    mov rsi, 4 * WORD_SIZE
    add rsi, rbp
    rep movsq
    mov qword [r10], rdx \n" in
    let make_closure_object = "MAKE_CLOSURE(rax, r10, " ^ lcode_counter ^ ")\n" in
    let last_jmp = "jmp " ^ lcont_counter ^ "\n" in
    let fix_opt = (match simple_or_opt with
    | 1 -> "
                pop rax ; rax = ret
                pop rbx ; rbx = lexical address
                pop rcx ; rcx = number of arguments entered
                mov rdx, " ^ (string_of_int (List.length params)) ^ " ; rdx = number of parm excpected
                mov r11, rcx
                sub r11, rdx ; arguments_entered - params_excpected
                inc r11
                cmp r11, 0
                je .push_back_args" ^ lambdaOpt_counter ^ "

                mov r10, rcx
                dec r10
                shl r10, 3
                mov rdi, rsp
                add rdi, r10  ;rsp -> one before last_arg

                mov r9, SOB_NIL_ADDRESS
                .loop_making_pair" ^ lambdaOpt_counter ^ ":
                    cmp r11, 0
                    je .push_result" ^ lambdaOpt_counter ^ "
                    dec r11
                    mov r8, qword [rdi]
                    MAKE_PAIR(r10, r8, r9)
                    mov r9, r10
                    sub rdi, WORD_SIZE
                    jmp .loop_making_pair" ^ lambdaOpt_counter ^ "
                .push_result" ^ lambdaOpt_counter ^ ":
                    add rdi, WORD_SIZE  ;push result at destined_place
                    mov qword [rdi], r9
                .push_back_args" ^ lambdaOpt_counter ^ ":
                    push rcx
                    push rbx
                    push rax


            "
    | _ -> ""
                  ) in
    let closure_body = lcode_counter ^ ":\n" ^ fix_opt ^
    "push rbp
    mov rbp , rsp\n" ^ body_str ^ "leave
    ret\n" ^ lcont_counter ^":\n" in
    allocate_ext_env ^ lex_env ^ copy_minor_envs ^ param_env_malloc ^  make_closure_object ^ last_jmp ^ closure_body
module Code_Gen : CODE_GEN = struct
  let make_consts_tbl asts = make_consts_tbl_local asts;;
  let make_fvars_tbl asts = make_fvars_tbl_local asts;;
  let generate consts fvars e = let e_renamed = (rename_tag_expressions (string_of_int (!ast_index)) e) in
                                ignore(ast_index := !ast_index + 1);
                                generate_local 1 consts fvars e_renamed;;
end;;




