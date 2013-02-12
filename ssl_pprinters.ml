(** This files contains the functions that allows to pretty print
any part of a SSL formula into a string of charcater.
*)

open Ssl_types
open Ssl
open SSL_lex
open Printf
open List



(** The fonctions that follow this part are use to pretty print
a ssl formula into the latex format *)


(*********************)
(*   Latex export    *)
(*********************)

let pprint_ssl_eq_tex eq =
  match  eq with
      Eqloc ( LVar (lg) , LVar(ld)) ->
	"\\EqLoc{"^lg^"}{"^ld^"}"

(** Prints an equation list into a string *)
let  pprint_ssl_eqlist_tex ( eqlist : eq list ) =
  let accu = "" in 
  let rec pprint_list_eq_fold fvisit l accu =
    match l with 
	[] -> accu
      |  h::l' ->
	if fvisit then 
	  pprint_list_eq_fold  false l' ( pprint_ssl_eq_tex h)
	else
	  pprint_list_eq_fold  false l' (accu^"\\wedge"^(pprint_ssl_eq_tex h)) 
  in
  pprint_list_eq_fold true eqlist accu


let pprint_ssl_affectation_tex table_aff =
  let accu = "" in
  let locvar_table_fold pvar lvar () accu =
    match pvar ,  lvar with 
	(PVar(pv) , LVar (lv)) ->  (accu^" \\wedge ("^pv^" \\mapsto "^lv^")")
  in
  let aff_table_fold pvar lvar_table accu =
    let ret_str = Hashtbl.fold (locvar_table_fold pvar) lvar_table accu
    in ret_str
  in
  let str_print =
    Hashtbl.fold aff_table_fold table_aff accu in
   str_print 

let pprint_ssl_ptnil_tex  ptnil_table =
  let accu = "" in
  let first_visit = ref true in
  let ptnil_folder pvar () accu =
    match pvar with 
	PVar ( vname ) ->
	    if !first_visit then 
	      begin
		first_visit := false ;
		(vname^"\\mapsto \\nil")
	      end
	    else
	      ( accu ^" \\wedge "^ vname^"\\mapsto \\nil")
  in
  let ret_string = (Hashtbl.fold ptnil_folder ptnil_table accu)
  in
  ret_string


let pprint_space_to_latex sformula =
 
  match sformula with 
      Space (heap_table) -> 
	if Hashtbl.length heap_table == 0
	then
	  "\\Emp"
	else
	  let nbelem = ref 0 in
	  let heap_print_folder lvar occurence accu =
	    match lvar with  
		LVar (vname ) -> 
		  begin
		  if !nbelem != 0 then 
		    begin
		    nbelem := !nbelem +1; 
		    accu ^"\\Unsep "^( sprintf "Alloc(%s,%i) " vname occurence)
		    end
		  else
		    (nbelem := !nbelem +1 ;
		    sprintf " Alloc(%s,%i) " vname occurence)
		  end
	  in
	  let ret_string = Hashtbl.fold heap_print_folder heap_table ""
	  in 
	  ret_string 
	    
    | Top_heap -> "\\top" 
      

let pprint_quant_vars_tex quant_vars_table = 
  let accu = "" in
  let locvar_table_fold lvar () accu =
    match lvar with 
	LVar (lv) -> 
	    ( accu ^ "\\exists " ^lv^".")
  in
  let ret_string = (Hashtbl.fold locvar_table_fold quant_vars_table accu)
  in
  ret_string


let pprint_pure_to_latex (sslf : ssl_formula ) =
  let accu = ref "" in
  begin
    let leneq = List.length sslf.pure.equations in
    let lenqvars = Hashtbl.length sslf.quant_vars in
    let lenaffect = Hashtbl.length sslf.pure.affectations in
    let len_ptnil =  Hashtbl.length sslf.pure.ptnil in
    if leneq > 0 then
      accu := !accu^(pprint_ssl_eqlist_tex sslf.pure.equations)^"\\wedge"; 
    if lenqvars > 0 then
      accu := (pprint_quant_vars_tex sslf.quant_vars) ;
     if  lenaffect+len_ptnil == 0
     then
       accu := !accu^"\\texttt{true}";
    if lenaffect > 0 then
      accu := (!accu)^(  pprint_ssl_affectation_tex sslf.pure.affectations) ;
    if len_ptnil > 0 then 
      begin 
	if lenaffect > 0 then
	  accu := (!accu)^"\\wedge "^(  pprint_ssl_ptnil_tex sslf.pure.ptnil)
	else
	  accu := (!accu)^(  pprint_ssl_ptnil_tex sslf.pure.ptnil)
      end
  end;
  !accu
  

  

let pprint_ssl_formula_tex (sslf : ssl_formula ) =
  let ret_str = "$"^"\\Formula{"^(pprint_pure_to_latex sslf)^"}{"^
    (pprint_space_to_latex sslf.space)^"}$" in
  ret_str
    


(** The fonction that*)
(** Prints an equation in a string*)






(*********************)
(**  Asci Export    **)
(*********************)


let pprint_ssl_eq eq =
  match  eq with
      Eqloc ( LVar (lg) , LVar(ld)) ->
	"("^lg^"=="^ld^")"

(** Prints an equation list into a string *)
let  pprint_ssl_eqlist ( eqlist : eq list ) =
  let accu = "Eq [" in 
  let rec pprint_list_eq_fold l accu =
    match l with 
	[] -> accu^"]"
      |  h::l' ->  pprint_list_eq_fold  l' (accu^";"^(pprint_ssl_eq h)) 
  in
  pprint_list_eq_fold eqlist accu


let pprint_ssl_affectation table_aff =
  let accu = "Aff [" in
  let locvar_table_fold pvar lvar () accu =
    match pvar ,  lvar with 
	(PVar(pv) , LVar (lv)) ->  (accu^";"^pv^"->"^lv)
  in
  let aff_table_fold pvar lvar_table accu =
    let ret_str = Hashtbl.fold (locvar_table_fold pvar) lvar_table accu
    in ret_str
  in
  let str_print =
    Hashtbl.fold aff_table_fold table_aff accu in
  ( str_print ^ "]")

let pprint_ssl_ptnil  ptnil_table =
  let accu = "Ptnil [" in
  let ptnil_folder pvar () accu =
    match pvar with 
	PVar ( vname ) ->   ( accu ^";"^ vname^"-> Nil")
  in
  let ret_string = Hashtbl.fold ptnil_folder ptnil_table accu in
  ( ret_string ^ "]")


let pprint_space_formula sformula =
  let heap_print_folder lvar occurence accu =
    match lvar with  
	LVar (vname ) -> accu ^"*"^( sprintf "Alloc(%s,%i)" vname occurence)
  in
  match sformula with 
      Space (heap_table) -> 
	if Hashtbl.length heap_table == 0
	then
	  "Emp"
	else
	  let ret_string = Hashtbl.fold heap_print_folder heap_table "Space ["
	  in 
	  (ret_string ^ "]")

    | Top_heap -> "Top_heap" 
  

let pprint_quant_vars quant_vars_table = 
  let accu = "Exists [ " in
  let locvar_table_fold lvar () accu =
    match   lvar with 
	LVar (lv) ->  ( accu ^ ";" ^ lv)
  in
  let ret_string = (Hashtbl.fold locvar_table_fold quant_vars_table accu)
  in
  (ret_string^ "]")

let pprint_ssl_formula (sslf : ssl_formula ) =
  let ret_str =
    (pprint_quant_vars sslf.quant_vars^"Pure{"^
    (pprint_ssl_eqlist sslf.pure.equations)
    ^(pprint_ssl_affectation sslf.pure.affectations)
   ^(pprint_ssl_ptnil sslf.pure.ptnil)
    ^"} || Space{"^(pprint_space_formula sslf.space)^"}") in
  ret_str



