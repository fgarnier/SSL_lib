(** This file contains some pretty printer which purpose consist in 
testing functions that will not be described in the final interface. 
They should not be linked with the final SSL library, but can be
kept for a debuging version. 
*)
(*
open Ssl_types
open Ssl_types.SSL_lex
open Ssl
open Format
open List
open Ssl_substitution
open Ssl_entailement
*)
(** Printing a list of equations *)


(**  Substitution into string *)
(*
let fold_substs (lvar : SSL_lex.locvar ) (rvar : SSL_lex.locvar) (previous : string ) =
  match lvar , rvar with 
      ( LVar(lname) , LVar(rname) ) ->  lname^"->"^rname^";"^previous


let subst_to_string ( subst : Ssl_substitution.loc_subst ) =
  match subst with
      Subst (table_subst ) -> 
	let ret_string = Hashtbl.fold fold_substs table_subst "" in
	"Subst [ "^ret_string^"]; \n"

let pprint_subst (out : Format.formatter ) ( subst :Ssl_substitution.loc_subst   ) =
  Format.fprintf out "%s" ( subst_to_string subst)
*)
 (*
let pprint_entailproblem (out : Format.formatter)(entp : Ssl_entailement.entail_problem) =
  Format.fprintf out "Left equation : \n";
  Ssl.pprint_ssl_formula out entp.left;
  Format.fprintf out "\n right equation : \n";
  Ssl.pprint_ssl_formula out entp.right;
  Format.fprintf out " \n%!"
  *)
