(** In this file we define the type of a substitution as well
as how to transfor the syntax of a SSL formula upon a substitution.

Athor : Florent Garnier.
write to first_name-dot-name-at-imag-dot-fr for question and/or comments.
*)


open Union_find
open List
open Hashtbl
open Ssl_types
open Ssl
open Ssl_types.SSL_lex

(* Keys : Domain of the substitutionm and values are the range *)
type loc_subst =  Subst of (locvar , locvar ) t

(** Creation of the identity substitution*)
let subst_id =
  let table = Hashtbl.create size_hash in
  Subst (table)

let eq_class_inversor  (repres : SSL_lex.locvar ) (lvars : SSL_lex.locvar )
    () (tble : (locvar , locvar) t) =
  Hashtbl.add tble lvars repres; tble 


(** Computes a substitution from a partition. Used in the normalization
algorithm. I.e : Equations -> Theories -> substitutions -> Normalization*)
let subst_from_partition (part : Union_find.partition ) =
  let inverse_image_folder (locv : SSL_lex.locvar) (eq_c : Union_find.eqclass)
      (table_subst : (locvar , locvar) t) =
    (Hashtbl.fold ( eq_class_inversor eq_c.repres ) eq_c.members table_subst)
   
  in    
  match part with 
      Partition (table_part ) -> let table = Hashtbl.fold  inverse_image_folder table_part (Hashtbl.create SSL_lex.size_hash) in
				 Subst (table)



(** Applies a substitution to the set of existancialy quantified vars
of a  SSL formula*)
let subst_against_quant_vars ( subst : loc_subst )( loctable : (locvar , unit) t) =
  let map_qvars subst_table lvar () =
    if Hashtbl.mem subst_table lvar then
      begin
	Hashtbl.remove loctable lvar;
	let nv_varname = Hashtbl.find subst_table lvar in
	if not (Hashtbl.mem loctable nv_varname )
	then  Hashtbl.add loctable nv_varname ()
	else ()
      end
  in
  match subst with
      Subst ( subst_table ) ->
	Hashtbl.iter (map_qvars subst_table ) loctable 
 
(* This fonction shall not appear in the ml-interface file *)

(** Applies a substitution against an equatio*)
let map_subst_list_eq (subst : loc_subst) ( equation : eq ) =
  let ret_eq = ref equation in
  match subst , equation with 
      ( Subst(subst_table) , Eqloc( xg , xd ) ) ->
	begin
	  if Hashtbl.mem subst_table xg 
	  then 
	    let xg' = Hashtbl.find subst_table xg in
	    ret_eq := Ssl.subst_loc xg xg' equation  
	end;
	begin
	  if  Hashtbl.mem subst_table xd 
	  then 
	    let xd' = Hashtbl.find subst_table xg in
	    ret_eq := Ssl.subst_loc xd xd' !ret_eq  
	end;
	!ret_eq
(** Maps the function above on an equation list.*)
let subst_against_eqlist (subst : loc_subst )( eqlist : eq list ) =
  List.map (map_subst_list_eq subst) eqlist
  

let subst_against_affectation (subst : loc_subst )(affect_table : ((SSL_lex.ptvar , (SSL_lex.locvar , unit) t ) t)) =
  let subst_map (subst_table : ((SSL_lex.locvar , SSL_lex.locvar ) t)) (current_table: (SSL_lex.locvar , unit) t ) (lvar : SSL_lex.locvar) () =
    if (( Hashtbl.mem subst_table lvar ) == true )
    then 
      begin
	Hashtbl.remove current_table lvar;
	let rvar =  Hashtbl.find subst_table lvar in 
	Hashtbl.add current_table rvar ()
      end
    else ()
  in
  let affect_table_iterator subst_table pvar lvar_table =
    Hashtbl.iter ( subst_map subst_table lvar_table ) lvar_table
  in
  match subst with 
      Subst ( table_subst ) ->
	Hashtbl.iter (affect_table_iterator table_subst ) affect_table


let subst_against_space (subst : loc_subst ) (sform : space_formula ) =
  let space_iterator (subst_table : (locvar, locvar ) t ) 
      ( current_table : (locvar , int) t ) lvar occur =
    if (( Hashtbl.mem subst_table lvar ) == true )
    then 
      begin
	let occ_lvar =  Hashtbl.find  current_table lvar in
	Hashtbl.remove current_table lvar;
	let rvar =  Hashtbl.find subst_table lvar in 
	add_alloc_occurences_space rvar occ_lvar (Space ( current_table ))
      end
    else ()
  in
  match sform , subst with 
      (Top_heap  , _ ) -> ()
    | (Space (table ) , Subst (subst_table) )  ->
      Hashtbl.iter (space_iterator subst_table table) table
      



(**
 Applies a substitution to a SSL formula. 
*TODO* One need to check the impact on quant_vars list. 

*)

(*let subst_agains_ssl (subst : loc_subst)(sformula : ssl_formula ) =
  {
    quant_vars = sformula.quant_vars;
    pure = {
      equations = subst_against_eqlist  subst sformula.pure.equations;
      affectations =  subst_against_affectation subst sformula.pure.affectations;
      ptnil = sformula.pure.ptnil; 
    };
    space = subst_against_space subst sformula.space
      
  }*)

(** Performs the same operation as above, but *)
 let subst_against_ssl (subst : loc_subst)(sformula : ssl_formula ) =
  
    
   subst_against_space subst sformula.space; subst_against_affectation subst sformula.pure.affectations; sformula.pure.equations <- (subst_against_eqlist subst sformula.pure.equations ) ; subst_against_quant_vars subst sformula.quant_vars
   

(** Compose_subst phi psi computes phi \odot psi. *)
 let compose_subst (subst_1 : loc_subst)(subst_2 : loc_subst) =
   let ret_table = Hashtbl.create size_hash in
   match subst_1 , subst_2 with
       ( Subst (table_1) , Subst (table_2) ) ->
	 let subst_2_iterator lvarg lvard =
	   if not ( Hashtbl.mem table_1 lvard ) then
	     Hashtbl.add ret_table lvarg lvard 
	   else 
	     let succs =  Hashtbl.find table_1 lvard in
	     Hashtbl.add ret_table lvarg succs 
	 in
	 let subst_1_iterator lvarg lvard =
	   if Hashtbl.mem ret_table lvarg then ()
	   else Hashtbl.add ret_table lvarg lvard
	 in
	 Hashtbl.iter subst_2_iterator table_2;
	 Hashtbl.iter subst_1_iterator table_1;
	 Subst(ret_table)
   
(**  
!!! Requires that the formula is in normal form !!!
 
This function deals with the case a location variable need to
be substituted by NIL. In this particular case, we do the following :

l is substituted by NIL in sslf, has the following semantic :
Any pointer var x such that x->l, is removed from the set of affectation,
and is moved into the set ptnil, and Ptnil(x) appears in sslf.pure.ptnils.

All \exists l in the set of quatified location variables are removed.

If alloc(l) apprers in the spacial formula, then the heap shall be
set to Top_heap, as alloc(NIL) is not a valid predicate.
*)
let subst_var_qvars_nil (lvar : locvar)(sslf : ssl_formula ) =
  Hashtbl.remove sslf.quant_vars lvar

(** This function requires that sslf is in normal form.*)
let subst_lvar_to_nil_in_affect (lvar : locvar)(sslf : ssl_formula ) =
  let remove_iterator banned_lvar pvar table_lvar =
    if Hashtbl.mem  table_lvar lvar then
      begin
	and_atomic_ptnil (Pointsnil(pvar)) sslf
      end
    else ()
  in
  Hashtbl.iter (remove_iterator lvar) sslf.pure.affectations

let subst_lvar_to_nil_in_heap (lvar : locvar ) ( sslf : ssl_formula ) =
  match sslf.space with
      Space (table) -> 
	begin
	  if Hashtbl.mem table lvar then
	    set_heap_to_top sslf
	  else ()
	end
    | Top_heap -> ()


let subst_to_nil_upon_sslf (lvar : locvar ) ( sslf : ssl_formula ) =
  subst_var_qvars_nil lvar sslf;
  subst_lvar_to_nil_in_affect lvar sslf;
  subst_lvar_to_nil_in_heap lvar sslf

