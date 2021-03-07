
#use "pc.ml";;
open PC

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Int of int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | TaggedSexpr of string * sexpr
  | TagRef of string;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | TaggedSexpr(name1, expr1), TaggedSexpr(name2, expr2) -> (name1 = name2) && (sexpr_eq expr1 expr2) 
  | TagRef(name1), TagRef(name2) -> name1 = name2
  | _ -> false;;

module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;


               (* GENERAL               *)

(* make_paired *)
let make_paired nt_left nt_right nt =
  let nt = caten nt_left (caten nt nt_right) in
  let nt = pack nt (fun ( _, (e, _)) -> e) in
  nt;;
 
 (* nts for symbols + not followed for num*)
  let punctuation = one_of "!$^*-_=+<:>/?";;
  let letter = range 'a' 'z';;
  let upLetter = range 'A' 'Z';;
  let notAnum = disj_list [punctuation ; letter; upLetter];;
 
 let convert_list_to_lower lst = List.map lowercase_ascii lst
 (*check if dup in list*)
 let rec dup_exist = function
   | [] -> false
   | head::tail -> List.exists ((=) head) tail || dup_exist tail
 (*                \GENERAL               *)
 (*                BOOLEAN PARSER               *)
 let nt_bool s = 
   let nt_true = pack (word_ci "#t") (fun (x) -> Bool(true)) in
   let nt_false = pack (word_ci "#f") (fun (x) -> Bool(false)) in
   let nt = disj nt_true nt_false in
   nt s;;
 (*                \BOOLEAN PARSER               *)
 
 (*                NUMBER PARSER               *)
 let digit = range '0' '9';;
 let sign = one_of "+-";;
 let digit_or_letter = disj_list [digit; upLetter; letter];;
 
 (*                HELPFUL FUNCS               *)
 let get_value_from_number_in_float x = match x with
 | Number Int value -> float_of_int value
 | Number Float value -> value
 | _ -> raise X_this_should_not_happen;;
 
 let get_value_of_letter_or_dig ch = match (lowercase_ascii ch) with
 | 'a' .. 'z' ->  ((int_of_char (lowercase_ascii ch)) - (int_of_char 'a')) + 10
 | '0' .. '9' -> (int_of_char ch) - (int_of_char '0')
 |  _ -> raise X_no_match;;
 
 let c_lst_to_base_real_num lst base = if (base > 36 || base <2 ) then raise X_no_match
 else
   List.fold_left (fun a b -> if(b<base) then base*a + b else raise X_no_match) 0 (List.map get_value_of_letter_or_dig lst);;
 
 let c_lst_to_base_frac_num lst base = List.fold_right (fun a b -> if(b<base) then a/.base +. b/.base else raise X_no_match) (List.map float_of_int (List.map get_value_of_letter_or_dig lst)) 0.;;
 (*                /HELPFUL FUNCS               *)
 
 (*RADIX PARSER*)
 let nt_radix s = let int_parser = pack (caten (maybe sign) (plus digit_or_letter)) (fun (sign, rest) ->
 if sign = Some '-' then (c_lst_to_base_real_num rest,c_lst_to_base_frac_num [], -1.)
 else (c_lst_to_base_real_num rest,c_lst_to_base_frac_num [], 1.))
 
 and float_parser = pack (caten (maybe sign) (caten (caten (plus digit_or_letter) (word ".")) (plus digit_or_letter))) (fun (sign, ((before_dot, dot), after_dot))-> 
 if sign = Some '-' then (c_lst_to_base_real_num before_dot, c_lst_to_base_frac_num after_dot, -1.)
 else (c_lst_to_base_real_num before_dot, c_lst_to_base_frac_num after_dot, 1.)
 ) in
 let nt_rad_pref = pack (make_paired (word "#") (word_ci "r") (plus digit)) (fun (x) -> int_of_string (list_to_string x))  in
 let nt_end = disj float_parser int_parser in
 let nt_combine = caten nt_rad_pref nt_end in
 let nt_combine = pack nt_combine (fun (t_base, t_lst)-> 
 match t_lst with
 | (x, y, z) -> let real_in = (float_of_int(x t_base)) in
                let frac_in = (y (float_of_int(t_base))) in
                let value = (real_in +. frac_in) *. z in
 if (frac_in = 0.0) then Number(Int (int_of_float value)) else Number (Float (value))
 ) in
 nt_combine s;;
 (*/RADIX PARSER*)
 let nt_number s = let int_parser = pack (caten (maybe sign) (plus digit)) (fun (sign, rest) ->
 if sign = Some '-' then Number (Int (int_of_string (list_to_string rest) * -1))
 else Number (Int (int_of_string (list_to_string rest))))
 
 and float_parser = pack (caten (maybe sign) (caten (caten (plus digit) (word ".")) (plus digit))) (fun (sign, ((before_dot, dot), after_dot))-> 
 if sign = Some '-' then Number (Float (float_of_string (("-")^(list_to_string before_dot)^(list_to_string dot)^(list_to_string after_dot))))
 else Number (Float ((float_of_string ((list_to_string before_dot)^(list_to_string dot)^(list_to_string after_dot)))))
 ) in
 let nt_scientific_notation = pack (caten (caten (disj float_parser int_parser) (word_ci "e")) int_parser) (fun((firstnum, e), secondnum)->  
 Number (Float ((get_value_from_number_in_float firstnum) *. (10.0**(get_value_from_number_in_float secondnum))))) in
 (not_followed_by (disj_list [nt_radix; nt_scientific_notation; float_parser; int_parser]) notAnum) s;;
 
 
 (*                \NUMBER PARSER               *)
 
 (*                SYMBOL PARSER               *)
 let up_to_low = pack upLetter (fun x-> lowercase_ascii x);;
 let nt_symbol_string = pack (plus (disj (disj (disj letter up_to_low) digit) punctuation)) (fun (sym) ->
 ((list_to_string(sym))));;
 
 let nt_symbol = pack (plus (disj (disj (disj letter up_to_low) digit) punctuation)) (fun (sym) ->
 Symbol ((list_to_string(sym))));;
 (*                \SYMBOL PARSER               *)
 
 (*                STRING PARSER               *)
 let convert_string char_list = match (list_to_string  char_list) with
 | "\\n" -> char_of_int 10
 | "\\r" -> char_of_int 13
 | "\\t" -> '\t'
 | "\\f" -> char_of_int 12
 | "\\\\" -> '\\'
 | "\\\"" -> char_of_int 34
 | _ -> raise X_no_match;;
 
 let nt_string_literal = diff nt_any (disj (char '\\') (char '\"'));;
 let nt_meta_char = disj_list [word_ci "\\n" ;word_ci "\\r" ;word_ci "\\t" ;word_ci "\\f" ;word_ci "\\\\" ;word_ci "\\\""];;
 let nt_acceptable_char = disj (pack nt_meta_char convert_string) nt_string_literal;;
 
 
 let nt_string = pack (caten (char '\"') (caten (star nt_acceptable_char) (char '\"'))) (fun(x, (y, z))->String (list_to_string y));;
 (*                \STRING PARSER               *)
 
 
 (*                CHAR PARSER               *)
 let convert_char char_list = match (list_to_string (convert_list_to_lower char_list)) with
   | "nul" -> char_of_int 0
   | "newline" -> char_of_int 10
   | "return" -> char_of_int 13
   | "tab" -> char_of_int 9
   | "page" -> char_of_int 12
   | "space" -> char_of_int 32
   | _ -> raise X_no_match;;
 
 let nt_named_char = disj_list [word_ci "nul" ; word_ci "newline" ; word_ci "return" ; word_ci "tab" ; word_ci "page" ; word_ci "space"];;
 let nt_visible_char = (const (fun(x)-> x>(char_of_int 32)));;
 
 let nt_prefix_char = (word "#\\");;
 let nt_char = pack (caten nt_prefix_char (disj (pack nt_named_char (fun (x) -> convert_char x)) nt_visible_char)) (fun(beginning, c)->Char(c));;
 
 (*                \CHAR PARSER               *)
 
 
 
 
 
  (* nt_skip - includes comments + whitespaces*)
  let rec nt_space = pack nt_whitespace (fun _ -> ())
  and nt_line_comment s = pack (make_paired (char ';')  (disj (char '\n') (pack nt_end_of_input (fun(x)->'\n'))) (star (diff nt_any (char '\n')))) (fun(_) -> ()) s
  and nt_sexpr_comment s = let nt = (caten(caten (word "#;") (star nt_skip))) (nt_sexp) in
  let nt = pack nt (fun _ -> ()) in
  nt s
  and nt_comment s = disj nt_line_comment nt_sexpr_comment s
  and nt_skip s = disj nt_comment nt_space s
  (*                NIL PARSER               *)
 and nt_nil s = pack (make_paired (char '(') (char ')') (star nt_skip)) (fun(x) -> Nil) s
 (*                \NIL PARSER               *)
 
  (*                LIST PARSER               *)
 and make_flat_list_from_pairs x = match x with
 | TaggedSexpr(tag_name, rest) -> List.append [tag_name] (make_flat_list_from_pairs rest)
 | Pair(first,second) -> List.append (make_flat_list_from_pairs first) (make_flat_list_from_pairs second)
 | _ -> []
 
 and nt_dot_list s =  pack (make_paired (char '(') (char ')') (caten (caten (plus nt_sexp) (word ".")) nt_sexp)) (fun ((x,y),z) -> (List.fold_right (fun a b -> Pair(a,b)) x z)) s
 and nt_reg_list s = pack (make_paired (char '(') (char ')') (star nt_sexp)) (fun y -> (List.fold_right (fun a b -> Pair(a, b)) y Nil)) s
 and nt_list_combine s =  disj nt_reg_list nt_dot_list s
 and nt_list s = let flat_dup_check =  pack nt_list_combine (fun original_value -> 
 if(dup_exist (make_flat_list_from_pairs original_value)) then raise X_this_should_not_happen else original_value
 ) in
 flat_dup_check s
 
 (*                \LIST PARSER               *)
 
 (*                Quote-like forms PARSER               *)
 and quote_match x y = match x with
 | '\'' -> Pair(Symbol ("quote"), Pair(y, Nil))
 | '`' -> Pair(Symbol ("quasiquote"), Pair(y, Nil))
 | ',' -> Pair(Symbol ("unquote"), Pair(y, Nil))
 | '@' -> Pair(Symbol ("unquote-splicing"), Pair(y, Nil))
 | _ -> raise X_no_match
 
 and quotes s = disj (pack (word ",@") (fun x-> '@')) (one_of "'`,") s
 and nt_qlf s = pack (caten quotes nt_sexp) (fun (x,y) -> quote_match x y) s
 (*                \Quote-like forms PARSER               *)
 
 (*                TagLife- PARSER               *)
 and nt_tag s = pack (caten (char '#') (make_paired (char '{') (char '}') nt_symbol_string))(fun(x,y)->y) s
 and nt_tag_expr s = let nt_check_tag = caten nt_tag (maybe (caten (char '=') nt_sexp)) in
 let nt_check_tag = pack nt_check_tag (fun (tag, x)-> match x with
 | Some('=', rest) ->  TaggedSexpr (tag, rest)
 | _  -> TagRef tag
 ) in
 nt_check_tag s
 
 and check_dup_texp first second = match second with
 | TaggedSexpr (x,y) -> if (x=first) then false else (check_dup_texp first y)
 | Pair(x, y) -> ((check_dup_texp first y) && (check_dup_texp first x))
 | _ -> true
 
 (*                /TagLife- PARSER               *)
 (*                Combined Parser               *)
 and nt_sexp s = let nt_sexpr = make_paired (star nt_skip) (star nt_skip) (disj_list [nt_bool ; nt_number ; nt_symbol ; nt_string ; nt_char ; nt_nil; nt_list; nt_qlf; nt_tag_expr]) in
 let nt_sexpr = pack nt_sexpr (fun (x)-> match x with
 | TaggedSexpr(first, second) -> if(check_dup_texp first second) then x else raise X_this_should_not_happen
 | _ -> x
 ) in 
 nt_sexpr s;;

let read_sexpr string = let (sexpr, rest) = nt_sexp (string_to_list string) in
if(rest==[]) then sexpr else raise X_no_match;;

let read_sexprs string = let (sexpr_list, rest) = (star nt_sexp (string_to_list string)) in sexpr_list

  

end;; (* struct Reader *)

