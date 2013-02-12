

open Ssl_types
open Ssl
open Ssl_types.SSL_lex
open Printf
open Format
open Union_find
open Hashtbl
open List
open Ssl_substitution
open Ssl_normalization
open Ssl_decision
open Debug_printers
open Ssl_entailement
open Ssl_biabduction


let pprint_garbage out garbage_table =
  let garbage_printer_it out lvar () =
    match lvar with 
	LVar(name) -> Format.fprintf out " %s ;" name
  in
  Format.fprintf out "Garbage list : [";
  Hashtbl.iter (garbage_printer_it out ) garbage_table;
  Format.fprintf out "] \n %!"




let main () =   	 
  let form = formatter_of_out_channel Pervasives.stdout in
  let phi_g = create_ssl_f () in
  let phi_d = create_ssl_f () in
  and_atomic_affect (Pointsto(PVar("x"),LVar("l1"))) phi_g;
  and_atomic_affect (Pointsto(PVar("y"),LVar("l2"))) phi_g;
  add_alloc_cell (LVar("l1")) phi_g;
  add_alloc_cell (LVar("l2")) phi_g;
  and_atomic_ptnil (Pointsnil(PVar("z"))) phi_g;
 (* and_atomic_ptnil (Pointsnil(PVar("z"))) phi_d;*)
  add_quant_var (LVar("l1")) phi_g;
  and_atomic_affect (Pointsto(PVar("x"),LVar("m1"))) phi_d;
  and_atomic_affect (Pointsto(PVar("y"),LVar("l2"))) phi_d;
  add_alloc_cell (LVar("l1")) phi_d;
  add_quant_var (LVar("m1")) phi_d;
  
  let entp = {left = phi_g; right = phi_d ;} in
  Format.fprintf form "********* Entailement problem ********* \n";
  pprint_entailproblem form entp;
  let biabduct_res = biabduction entp in
  Format.fprintf form "********* Entailement problem After biabduction ********* \n";
  Format.fprintf form "********* Enunciate after renaming ********* \n";
  pprint_entailproblem form biabduct_res.enunciate;
  Format.fprintf form "********* Frame and antiframe ********* \n";
  pprint_entailproblem form biabduct_res.frame_antiframe;
  let left_garbage =  garbage_exists_lvar_heap biabduct_res.frame_antiframe.left in
  let right_garbage = garbage_exists_lvar_heap biabduct_res.frame_antiframe.right in
  Format.fprintf form "Garbage in lhs \n";
  pprint_garbage form left_garbage;
  Format.fprintf form "Garbage of rhds \n";
  pprint_garbage form right_garbage;

  Format.fprintf form " Star of Frame * left and Antiframe * right \n";
  let etpf = { 
    left = (star_sep biabduct_res.enunciate.left biabduct_res.frame_antiframe.right ) ;
    right = (star_sep biabduct_res.enunciate.right biabduct_res.frame_antiframe.left ) 
  } in
  begin
    if sat_ssl etpf.left && sat_ssl etpf.right then
      Format.fprintf form " Biabduction is satifiable \n %!"
    else
      Format.fprintf form " Biabduction is unsat \n %!"
  end;
  pprint_entailproblem form etpf;
  Format.fprintf form " computing the entailement of the previous entailement \n";
  Format.fprintf form "Garbage of left \n";
  ssl_entailement etpf;
  pprint_entailproblem form etpf
  
  
	 



           


let () = main ()
