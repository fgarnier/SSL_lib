open Union_find
open List
open Hashtbl
open Ssl_types
open Ssl
open Ssl_types.SSL_lex
open Ssl_substitution
open Ssl_normalization


exception SSL_unsat
exception No_locvars_left
exception Lvar_present
exception Not_pointed


let is_rel_in ( pvar : ptvar ) (lvar : locvar) ( sslf : ssl_formula ) =
  let ptable = sslf.pure.affectations in
    try
      let ptvar_bounds = Hashtbl.find ptable pvar in
	Hashtbl.mem  ptvar_bounds lvar (* If some ptvar->l bindings are 
				      present, check that ptvar->lvar is
				      indeed registered.*)
    with
 	Not_found -> false (* there's no such pvar->l, hence the answer
			   is false*)


(** This function returns true if lvar isn't a bounded var
of sslf and has at least on occurence of lvar*)
let free_var (sslf : ssl_formula)(lvar : locvar ) =
  not ( Hashtbl.mem sslf.quant_vars lvar )  && ssl_contains_locvar lvar sslf

(** A SSL formula in normal form is sat iff 
_ Each loc var that appears on the heap appears once
_ There is no x->l and x->nil and Alloc(l) on the heap
*)
let sat_ssl (sslf : ssl_formula ) =
  let fold_spacial _ occurences _ =
    if occurences > 1 then raise SSL_unsat
    else true
  in
  try
    match sslf.space with
	Space (space_f) ->
	  let heap_sat = ( Hashtbl.fold fold_spacial space_f true )
	  in heap_sat
      | Top_heap -> false
  with
      SSL_unsat -> false
	
  

(** A formula is garbage if it contains an allocated cell which
base address is not pointed by a pointer variable*)
let is_locvar_pointed_at (lvar :locvar ) ( puref : pure_formula ) =
  let aff_iterator _ table_lvar =
    if (Hashtbl.mem table_lvar lvar )
    then raise Lvar_present
    else ()
  in
  if Hashtbl.length puref.affectations == 0 then false else
    try
      Hashtbl.iter aff_iterator puref.affectations; false
    with
	Lvar_present -> true
	  
(** Returns true if the heap contains some garbage.*)
let garbage_ssl (sslf : ssl_formula ) =
  let space_iterator lvar _ =
    if (is_locvar_pointed_at lvar sslf.pure ) == false then
      raise Not_pointed 
    else ()
  in
  match sslf.space with 
      Top_heap -> false
    | Space ( table_space ) ->
	try
	  Hashtbl.iter space_iterator table_space;
	  false (* If the iteration completes then there is no
		unreferenced loc vars in the heap*)
	with
 	    Not_pointed -> true

	      (* However, in this case there is one unreferenced
	      var in the heap*)



  
