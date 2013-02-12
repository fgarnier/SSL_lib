(** This files contains the fonctions and the definitions required
to decide the entailement property. 

Mail_to florent dot garnier at imag dot fr, for questions, comments
or requests.

*)

open Hashtbl
open List
open Ssl_types 
open Ssl
open Ssl_normalization
open SSL_lex
open Ssl_substitution
open Ssl_decision
open Ssl_pprinters
(*open Self*)



exception No_more_vars


type entail_problem = {left : ssl_formula ; right : ssl_formula ;}
type entail_subst = {lsubst : loc_subst ; rsubst : loc_subst ;}
type fresh_loc_var = FLVar of string * int

let entail_subst_id  =
  { rsubst = subst_id;
    lsubst = subst_id;
  }


let flvar_to_locvar fvar = 
  match fvar with
      FLVar (name , c ) -> LVar ( (Format.sprintf "%s_%d" name c ) )

(** On elimine les x ->l  ... |- x-> l
*)

let fresh_flvar (flvar : fresh_loc_var ) =
  match flvar with
      FLVar  (name , c ) ->  FLVar (name , (c+1))

(** Computes the name of a location variable, that is fresh for both
SSL formulae of the entailement problem
*)

(** returns the set of the existencially quantified locvar of the heap,
that are not pointed at by any pointer variables. *)
let garbage_exists_lvar_heap ( sslf : ssl_formula ) =
  let ret = Hashtbl.create SSL_lex.size_hash in
  let garb_iterator lvar _ =
    if (is_exists_quantified lvar sslf) && (not (is_locvar_pointed_at lvar sslf.pure )) && space_contains_locvar lvar sslf.space
    then
      Hashtbl.add ret lvar ()
  in
    match sslf.space with
	Space (space_table ) ->
	  Hashtbl.iter garb_iterator space_table; ret
      | Top_heap -> ret
  

let fresh_locvar_name_from_etp (etp : entail_problem ) =
  let max_varloc_name_lex_fold_affect_table lvar () lvar_param =
    if Ssl.cmp_lex_lvar lvar lvar_param
    then lvar
    else lvar_param
  in
  let max_varloc_name_lex_fold_table _ loctable lvar_param =
    let maxtbl = Hashtbl.fold max_varloc_name_lex_fold_affect_table loctable lvar_param  in
    if Ssl.cmp_lex_lvar maxtbl lvar_param then
      maxtbl
    else
      lvar_param
  in
  let max_varloc_name_space_fold  lvar _ lvar_param =
    if cmp_lex_lvar lvar lvar_param
    then lvar
    else lvar_param
  in
  let var_max = Hashtbl.fold max_varloc_name_lex_fold_table etp.left.pure.affectations (LVar("")) in
  let var_max = Hashtbl.fold max_varloc_name_lex_fold_table etp.right.pure.affectations var_max in
  let  var_max = Hashtbl.fold  max_varloc_name_lex_fold_affect_table etp.left.quant_vars var_max  in
  let  var_max = Hashtbl.fold  max_varloc_name_lex_fold_affect_table etp.right.quant_vars var_max in
  match etp.left.space , etp.right.space with
      ( Space(tableg) , Space(tabled) ) ->
	begin
	  let  var_max =  Hashtbl.fold max_varloc_name_space_fold tableg var_max in
	  let  var_max =  Hashtbl.fold max_varloc_name_space_fold tabled var_max in
	  match var_max with
	      LVar ( vname ) -> FLVar( vname, 1)
	end
    |  ( Space(tableg) , _ ) -> 
      begin
	let var_max = Hashtbl.fold max_varloc_name_space_fold tableg var_max in
	match var_max with
	    LVar ( vname ) -> FLVar( vname, 1)
      end

    |  ( _ ,  Space(tabled) ) -> 
      begin
	let var_max = Hashtbl.fold max_varloc_name_space_fold tabled var_max in
	match var_max with
	    LVar ( vname ) -> FLVar( vname, 1)
      end
	
      
    | (_,_) -> 
      match var_max with
	  LVar ( vname ) -> FLVar( vname, 1)
	    (*raise Top_heap_exception*) 
  

(** Used to compute the biggest location variabl in a (locvar, unit ) t 
Hash table.*)
let varname_folder lvar () lvar_arg =
  if cmp_lex_lvar lvar lvar_arg then
    lvar 
  else lvar_arg
 
let entail_r1  ( etp : entail_problem ) = 
  let r1_iterator pvar loctable  =
    if Hashtbl.mem etp.right.pure.affectations pvar then
    let lvar_rel = pick_first_lvar loctable  in
    let pvar_right = Hashtbl.find etp.right.pure.affectations pvar in
    if Hashtbl.mem pvar_right lvar_rel then
      if  ( not ( Hashtbl.mem etp.right.quant_vars lvar_rel )  ) &&  ( not ( Hashtbl.mem etp.left.quant_vars lvar_rel ) ) 
      then
	begin
	  Hashtbl.remove etp.right.pure.affectations pvar; 
	  Hashtbl.remove etp.left.pure.affectations pvar
	end
    else ()
  in
  Hashtbl.iter r1_iterator etp.left.pure.affectations
  

let entail_r1_nil (etp : entail_problem ) =
  let remove_ptnil_iterator pvar _ =
    if Hashtbl.mem etp.right.pure.ptnil pvar
    then
      begin
	Hashtbl.remove etp.left.pure.ptnil pvar;
	Hashtbl.remove etp.right.pure.ptnil pvar
      end
    else ()
  in
  Hashtbl.iter remove_ptnil_iterator etp.left.pure.ptnil

(** For all x->l, where l is free, of the lhs, r_3 seeks a x->l' of
the rhs, where l' is bounded. If such an affectation exists then 
x->l, resp x->l' are removed from their respective equations,
and l' is substituted by a fresh varible in the reminder of the
rhs of the entailement.*)
let entail_r3 (etp : entail_problem ) =
  let left_aff_iterator pvar ltable =
    let lvar_left = pick_first_lvar ltable in
    if free_var  etp.left lvar_left then
      try 
	let lvar_table_right = Hashtbl.find etp.right.pure.affectations pvar
	in
	let lvar_right = pick_first_lvar lvar_table_right in
	if is_exists_quantified lvar_right etp.right then
	  let subst_table = Hashtbl.create size_hash in
	  Hashtbl.add subst_table lvar_right lvar_left;
	  Hashtbl.remove etp.right.pure.affectations pvar;
	  Hashtbl.remove etp.left.pure.affectations pvar;
	  let right_subst = (Subst(subst_table)) in
	  subst_against_ssl right_subst etp.right
      with
	  Not_found -> ()
    else ()
  in
  Hashtbl.iter left_aff_iterator etp.left.pure.affectations

(** For all   (x->nil/\ Phi |- \exists l x->l /\Psi) 
    rewrite to Phi |- Psi[Nil <- l]
*)
let entail_r3_nil (etp : entail_problem) = 
  let pt_nil_remove_iterator pvar _ = 
     try
       let lvar_table_right = Hashtbl.find etp.right.pure.affectations pvar in
       let lvar_right = pick_first_lvar lvar_table_right in
	if is_exists_quantified lvar_right etp.right then
	  begin
	    Hashtbl.remove etp.left.pure.ptnil pvar;
	    Hashtbl.remove etp.right.pure.affectations pvar;
	    subst_to_nil_upon_sslf lvar_right etp.right
	  end
	else ()
     with
	 Not_found ->  ()
  in 
  Hashtbl.iter pt_nil_remove_iterator etp.left.pure.ptnil




(** The first optional parameter can be used to compute the composition
of all the substitutions used to reduce the entailement problem. This
information is needed by the biabduction procedure.
 *)
let entail_r4 ( subst_ref : (entail_subst ref) option )( etp : entail_problem ) =
  let r4_iterator pvar loctable  =
    if Hashtbl.mem etp.left.pure.affectations pvar then
    (*let lvar_rel = Hashtbl.fold varname_folder loctable (LVar("")) in*)
    (*begin match lvar_rel with 
	LVar(varname ) ->
	  Format.printf " lvar_rel = %s \n" varname 
    end;*)
    let pvar_left_table = Hashtbl.find etp.left.pure.affectations pvar in
    let locv_right =  pick_first_lvar  loctable in
    let locv_left =  pick_first_lvar (pvar_left_table) in
      if   ((is_exists_quantified  locv_right etp.right)
	&&   ( is_exists_quantified  locv_left etp.left) )
      then
	begin
	  (*try*) 
	    let fresh_flvar = 
	      fresh_locvar_name_from_etp etp in
	    let fresh_lvar = flvar_to_locvar fresh_flvar in
	    let subst_table_left = Hashtbl.create SSL_lex.size_hash in
	    let subst_table_right = Hashtbl.create SSL_lex.size_hash in
	    Hashtbl.add subst_table_left locv_left fresh_lvar;
	    Hashtbl.add subst_table_right locv_right fresh_lvar;
	    let subst_left = Subst ( subst_table_left ) in
	    let subst_right = Subst ( subst_table_right ) in
	    Hashtbl.remove etp.right.pure.affectations pvar; 
	    Hashtbl.remove etp.left.pure.affectations pvar ;
	    subst_against_ssl subst_right etp.right;
	    subst_against_ssl subst_left etp.left;
	 


	      match subst_ref with 
		  Some ( overall_subst ) -> 
		    overall_subst := 
		      {lsubst = (Ssl_substitution.compose_subst subst_left !overall_subst.rsubst );
		       rsubst = (Ssl_substitution.compose_subst subst_right !overall_subst.lsubst );
		}
		| None -> ()
 
	 (* with
	      Top_heap_exception -> ()*)
	end
  in
  Hashtbl.iter r4_iterator etp.right.pure.affectations;
  var_elim etp.left;
  var_elim etp.right


(** rule r_5 : 
   Removes any couples alloc(l) , \exists l' alloc(l') where alloc(l) is
    a garbage of the
    lhs and alloc(l') is in  the rhs, and when l is a FV 
*)
let entail_r5 (entp : entail_problem ) =
  let lhs_heap_iterator rhs_garbage_table lhs_heap_table rhs_heap_table lvar occurences =
    if Hashtbl.length rhs_garbage_table == 0
    then raise No_more_vars 
    else
      if (free_var entp.left lvar) &&  not ( is_locvar_pointed_at lvar entp.left.pure ) && ( occurences == 1 )
      then
	try
	  let garb_lvar = pick_first_lvar rhs_garbage_table in
	  if (Hashtbl.find rhs_heap_table garb_lvar)!=1
	  then raise Top_heap_exception
	  else
	    begin
	      Hashtbl.remove rhs_garbage_table garb_lvar;
	      Hashtbl.remove lhs_heap_table lvar;
	      Hashtbl.remove rhs_heap_table garb_lvar
	    end
	with
	    Not_found -> ()
in
let right_garbage = garbage_exists_lvar_heap entp.right in
match entp.left.space,  entp.right.space with
    ( Space ( space_table_left ) , Space (space_table_right) )-> 
      begin
	try
	  Hashtbl.iter (lhs_heap_iterator right_garbage space_table_left space_table_right) space_table_left
	with
	    No_more_vars -> ()
	  | Top_heap_exception -> raise Top_heap_exception
	  (* The iterator can raise a Top_heap_exception. We propagate
	  the exception in this case.*)
      end
  | (_,_) -> ()  (** No operation is performed when one heap is fubar.*)

    (* raise Top_heap_exception *)
    (* In this case, at leat on of the heap are corrupted, hence we
    raise an exception to note that one can't infer a new heap.*)

let entail_ptnil ( etp : entail_problem ) =
  (* one iterates on rhs equation*)
  let ptnil_iterator pvar () =
    if Hashtbl.mem etp.left.pure.ptnil pvar 
    then 
      begin
	Hashtbl.remove etp.left.pure.ptnil pvar;
	Hashtbl.remove etp.right.pure.ptnil pvar
      end
  in
  Hashtbl.iter ptnil_iterator etp.right.pure.ptnil

let entail_r2 ( etp : entail_problem ) =
  let r2_iterator lvar occurence  =
    if occurence != 1 then ()
    else
      match etp.left.space ,  etp.right.space with
	  (Space (space_table_left) , Space (space_table_right )) ->
	    if Hashtbl.mem space_table_right lvar then
	      let occurence_right = Hashtbl.find space_table_right lvar in
	      (* Both locvar are free vars in both equations *)   
	      if  (free_var  etp.left lvar ) && ( free_var etp.right lvar ) && (occurence_right == 1)
	      then
		begin
		  Hashtbl.remove space_table_left lvar;
		  Hashtbl.remove space_table_right lvar
		end
	      else ()
	| (_,_) -> () (* Do nothing if the heaps aren't both in sane shape*)
	    (*raise Top_heap_exception*)
  in
  try
    match  etp.left.space with
	Space( space_table_left ) -> Hashtbl.iter r2_iterator space_table_left
      | Top_heap -> () (*Left heap is corrupted, then skip rule 2.*) 
	  (**)
  with 
      Top_heap_exception -> raise Top_heap_exception




let entail_r6 (etp : entail_problem ) =
(*  Used to iterate on the garbage variables of the right h.s. of the 
entailement.*)
  let del_garbage_iterator table_g table_d garbage_g lvar () =
    let occurences = Hashtbl.find table_d lvar in
    if occurences != 1 then ()
    else 
      if ( Hashtbl.length table_g ) == 0
      then raise No_more_vars
      else 
	let lvar_g = pick_first_lvar garbage_g in
	begin
	  match lvar_g with 
	      LVar("") -> ()
	    | LVar(value) ->
	      let occ_lvard = Hashtbl.find table_g lvar_g in
	      if occ_lvard == 1 then
		begin
		  Hashtbl.remove table_d lvar;
		  Hashtbl.remove table_g lvar_g;
		  Hashtbl.remove garbage_g lvar_g
		end
	      else ()
	end
	  
  in
  let garb_left = garbage_exists_lvar_heap etp.left in
  let garb_right = garbage_exists_lvar_heap etp.right in
 
  match etp.left.space , etp.right.space with
      (Space (table_g) , Space (table_d)) ->
	begin
	  try
	    Hashtbl.iter (del_garbage_iterator table_g table_d garb_left) garb_right (* Ssl_normalization.var_elim etp.left; Ssl_normalization.var_elim etp.right*)
	  with
	      No_more_vars -> ()
	end
    | (_,_) -> ()




(** Reduces an entailement problem.*)
let ssl_entailement (etp : entail_problem ) =
 
  let overall_subst =  ref (entail_subst_id) in
  normalize_ssl etp.left;
  normalize_ssl etp.right;
  entail_r4 (Some(overall_subst)) etp;
  subst_against_ssl !overall_subst.lsubst etp.left;
  subst_against_ssl !overall_subst.rsubst etp.right;
  entail_r2 etp;
  entail_r6 etp;
  entail_r1 etp;
  entail_r1_nil etp;
  entail_r3 etp;
  entail_r3_nil etp;
  entail_r5 etp
 




let pprint_entailement_problem (etp : entail_problem ) =
  let ret_str = "\n******************** \n Left  formula : \n "^(pprint_ssl_formula etp.left)^"\n Right formula  \n"^(pprint_ssl_formula etp.right)^"\n*********************** \n" in
  ret_str


(** decides whether a f |- g is true, that's to say
that f |- g reduces to 
(Pure[...]|| Emp ) |- (true || Emp)

the entailement problem and their associated SSL formulae
are copied, and the parameter remain unaffected by the
computation. Both formulae of the entailement problem must
be in normal form.
*)
let does_entail (etp : entail_problem ) =
  let etp_prime = { 
    left = (Ssl.copy etp.left) ;
    right = (Ssl.copy etp.right) ;
  } 
  in
  (*Self.feedback ~level:0 "I reached does_entail \n";
  Format.printf " \n [ does_entail ] %s \n " (pprint_entailement_problem etp);*)  
  begin
    try 
      ssl_entailement etp_prime;
    with
	Top_heap_exception -> raise Top_heap_exception          
	  (** We shall not deal with exception
					at this point. This treatment is here
					for testing purpose, until a proper
					exception treatment is added in the
					Ecfg computation function/method. *)
	  
  end;
  match etp_prime.left.space , etp_prime.right.space with 
      ( Space ( space_table_l) , Space(space_table_r)) ->
	begin
	  if ( Hashtbl.length space_table_l > 0 ) ||
	    (Hashtbl.length space_table_r > 0 ) then
	      begin
		Printf.printf " \n [ does_entail ] FALSE, heap of different size \n";
		false
	      end
	  else
		begin
		  if (Hashtbl.length etp_prime.right.pure.affectations == 0 )
		    && (Hashtbl.length etp_prime.right.pure.ptnil == 0)
		  then
		    begin
		      Printf.printf " \n [ does_entail ] TRUE, empty rigth formula \n";
		      true
		    end
		  else
		    begin
		      Printf.printf " \n [ does_entail ] FALSE, non empty right formula \n";
		      Format.printf " \n [ False : Post computations : ] %s \n " (pprint_entailement_problem etp_prime);
		      
		      
		      false
		    end
		end
	end
    | (Top_heap,Top_heap) ->
	Printf.printf " \n [ does_entail ] TRUE, both  formula has
 Top Heap \n";
	true (** One of the heap is broken, shall raise an
		 exception.*)
    |(_,_)->
       Printf.printf "\n  [ does_entail ] FALSE, ONE fromula has
Top Heapm while the other one hasn't \n";
       false (* One heap is broken whilst the other on isn't, hence
		no entailement relation between those two incomparable
		formulae.*)
 

	  

  
  


let accept_new_abstraction (etp : entail_problem ) =
  let etp_prime = { 
    left = (Ssl.copy etp.left) ;
    right = (Ssl.copy etp.right) ;
  } 
  in
  (*Self.feedback ~level:0 "I reached does_entail \n";
  Format.printf " \n [ accept_new_abstraction ] %s \n " (pprint_entailement_problem etp);*)  
  begin
(*    try *)
      ssl_entailement etp_prime
   (* with *
	Top_heap_exception -> raise Top_heap_exception *)        
	  (** We shall not deal with exception
					at this point. This treatment is here
					for testing purpose, until a proper
					exception treatment is added in the
					Ecfg computation function/method. *)
	  
  end;
  match etp_prime.left.space , etp_prime.right.space with 
      ( Space ( space_table_l) , Space(space_table_r)) ->
	begin
	  if ( Hashtbl.length space_table_l > 0 ) ||
	    (Hashtbl.length space_table_r > 0 ) then
	      begin
		Printf.printf " \n [ accept_entailement ] TRUE, heap of different size \n";
		true
	      end
	  else
		begin
		  if (Hashtbl.length etp_prime.right.pure.affectations == 0 )
		    && (Hashtbl.length etp_prime.right.pure.ptnil == 0)
		  then
		    begin
		      Printf.printf " \n [ accept_entailenebt ] FALSE, rigth formula is entailed by a more precise one\n";
		      false
		    end
		  else
		    begin
		      Printf.printf " \n [  accept_entailement ] TRUE, non empty right formula, meaning it is not comparable with the left hand side \n";
		      Format.printf " \n [ True : Post computations : ] %s \n " (pprint_entailement_problem etp_prime);
		      
		      
		      true
		    end
		end
	end
    | (Top_heap,Top_heap) ->
	Printf.printf " \n [ accept_new_abstraction ] false, False formula aren't
added, as all are equivalent ";
	false (** One of the heap is broken, shall raise an
		 exception.*)
    |(_,Top_heap)->
       Printf.printf "\n  [ accept_new_abstraction ] true , Rhs has Top_heap
whilst Lhs don't, accepting it";
       true  (* One heap is broken whilst the other on isn't, hence
		no entailement relation between those two incomparable
		formulae.*)
 
    |(Top_heap,_) ->
       Printf.printf "\n  [ accept_new_abstraction ] false, Rhs has not Top_heap
whilst Lhs has, accepting it";
       false



(* This function decides whether an abstract states needs to be added
*)
let entails_abstraction_adder (etp : entail_problem ) =
  let etp_prime = { 
    left = (Ssl.copy etp.left) ;
    right = (Ssl.copy etp.right) ;
  } 
  in
  (*Self.feedback ~level:0 " In entails_abstraction_adder \n";
  Format.printf " \n [ entails_abstraction_adder : ] %s \n " (pprint_entailement_problem etp); *) 
  begin
(*    try *)
      ssl_entailement etp_prime;
    (*Format.fprintf Ast_goodies.debug_out "[entails_abstraction_adder ] ETP after call to entailement %s " (pprint_entailement_problem etp_prime);*)
   (* with *
	Top_heap_exception -> raise Top_heap_exception *)        
	  (** We shall not deal with exception
					at this point. This treatment is here
					for testing purpose, until a proper
					exception treatment is added in the
					Ecfg computation function/method. *)
	  
  end;
  match etp_prime.left.space , etp_prime.right.space with 
      ( Space ( space_table_l) , Space(space_table_r)) ->
	begin
	  if (( Hashtbl.length space_table_l > 0 ) ||
	    (Hashtbl.length space_table_r > 0 )) 
	  then
	    begin
	      Format.fprintf Ast_goodies.debug_out  " \n [ entails_abstraction_adder ] Add rhs formula, heap of different size \n";
	      Format.fprintf  Ast_goodies.debug_out " \n [ entails_abstraction_adder Post computations : ] %s \n " (pprint_entailement_problem etp_prime);
	      false
	    end
	  else
	    begin
	      if( (Hashtbl.length etp_prime.right.pure.affectations == 0 )
		&& (Hashtbl.length etp_prime.right.pure.ptnil == 0))
	      then
		begin
		  Format.fprintf Ast_goodies.debug_out  " \n [entails_abstraction_adder] Don't add, rigth formula is entailed by a more precise one\n";
		  Format.fprintf  Ast_goodies.debug_out " \n [entails_abstraction_addder :] Entailement holds : Post computation %s \n " (pprint_entailement_problem etp_prime);
		  true
		end
	      else
		begin
		  Format.fprintf Ast_goodies.debug_out " \n [entails_abstraction_adder] Rhs not entailed by Lhs as non empty right formula, meaning it is not comparable with the left hand side \n";
		  Format.fprintf  Ast_goodies.debug_out " \n [ entails_abstraction Post computations : ] %s \n " (pprint_entailement_problem etp_prime);
		  false
		end
	    end
	end
    | (Top_heap,Top_heap) ->
	Format.fprintf  Ast_goodies.debug_out " \n [ entails abstraction adder ] (Top,Top) Lhs entails RHS , as both have a broken heap ";
	true (** One of the heap is broken, shall raise an
		 exception.*)
    |(_,Top_heap)->
       Format.fprintf  Ast_goodies.debug_out "\n  [ entails abstraction adder ] (_,Top) Lhs does not entails Rhs has Top_heap";
       false  (* One heap is broken whilst the other on isn't, hence
		no entailement relation between those two incomparable
		formulae.*)
 
    |(Top_heap,_) ->
       Format.fprintf  Ast_goodies.debug_out "\n  [ entails abstraction adder ] (Top,_) Lhs does not etails Rhs has not Top_heap
whilst Lhs has, accepting it";
       false

    
