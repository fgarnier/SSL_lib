(** This files contains the implementation of the biabduction algorithm.*)

open Ssl_types
open Ssl
open SSL_lex
open Ssl_entailement
open Ssl_normalization
open Ssl_substitution


type biabduct_sol = {
enunciate : entail_problem ;
frame_antiframe : entail_problem ;
}



let fold_substs (lvar : SSL_lex.locvar ) (rvar : SSL_lex.locvar) (previous : string ) =
  match lvar , rvar with 
      ( LVar(lname) , LVar(rname) ) ->  lname^"->"^rname^";"^previous


let subst_to_string ( subst : Ssl_substitution.loc_subst ) =
  match subst with
      Subst (table_subst ) -> 
	let ret_string = Hashtbl.fold fold_substs table_subst "" in
	"Subst [ "^ret_string^"]; \n"



(** Takes as input an entailement problem and returns the
a biabduction_sol structures such that :

 _ enunciate is a entailement problem which both formulae are
logically equivalent to the correspondig etp formulae.
_ frame_antiframe contains two formulae such that :
     enunciate.left *  frame_antiframe.right |- enunciate.right *  frame_antiframe.left \leadsto (true|Emp) |- (true |Emp) iff the biabdcution problem is SAT. 
*)
let biabduction (etp : entail_problem ) =
  let overall_subst =  ref (entail_subst_id) in
  normalize_ssl etp.left;
  normalize_ssl etp.right;
  let enun = { left = (Ssl.copy etp.left) ; right =( Ssl.copy etp.right) } in
 
  Format.printf " ***** \n Debug : lsubst  %s \n **** %!" ( subst_to_string !overall_subst.lsubst );
  
   Format.printf " ***** \n Debug : rsubst  %s \n **** %!" ( subst_to_string !overall_subst.rsubst );
  
  entail_r4 (Some(overall_subst)) etp;
   
  Format.printf " ***** \n Debug : lsubst %s \n **** %!" ( subst_to_string !overall_subst.lsubst );
   Format.printf " ***** \n Debug : rsubst  %s \n **** %!" ( subst_to_string !overall_subst.rsubst );
  
  subst_against_ssl !overall_subst.lsubst enun.left;
  subst_against_ssl !overall_subst.rsubst enun.right;
 
  (*subst_against_ssl !overall_subst etp.left;
  subst_against_ssl !overall_subst etp.right;*)
 
  entail_r1 etp;
  entail_r2 etp;
  entail_ptnil etp;
  entail_r6 etp;
  
   let ret = {
    enunciate = enun;
    frame_antiframe = etp
  } in ret
  
  

  
  
