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

let main () =
   let newf = Ssl.create_ssl_f () in
   and_atomic_eq (Eqloc(LVar("l_1"),LVar("l_4"))) newf;
   and_atomic_eq (Eqloc(LVar("l_4"),LVar("l_5"))) newf;  
   and_atomic_eq (Eqloc(LVar("l_2"),LVar("l_4"))) newf;
   and_atomic_ptnil (Pointsnil(PVar("x"))) newf;
   add_quant_var (LVar("l_1")) newf;
   and_atomic_affect (Pointsto(PVar("y"),LVar("l1"))) newf;
   add_alloc_cell (LVar("y")) newf ;
   add_alloc_cell (LVar("y")) newf ;
   add_alloc_cell (LVar("x")) newf ;
   let newf2 =Ssl.create_ssl_f () in
    add_quant_var(LVar("l_1")) newf2; add_quant_var(LVar("l_5")) newf2;
   and_atomic_ptnil (Pointsnil(PVar("x1"))) newf2; 
   and_atomic_affect (Pointsto(PVar("y1"),LVar("l3"))) newf2;
   add_alloc_cell (LVar("y")) newf2 ;
   add_alloc_cell (LVar("y4")) newf2 ;
   add_alloc_cell (LVar("x6")) newf2 ;
   let f4 = star_sep newf newf2 in
   let form = formatter_of_out_channel Pervasives.stdout in
   Ssl.pprint_ssl_formula form f4 ;
   Format.fprintf form "%!"  ;
   Format.fprintf form "\n Testing unify eq loc \n";
   let test_unif_eq = Ssl.create_ssl_f () in
   and_atomic_affect (Pointsto(PVar("y1"),LVar("l3"))) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("y1"),LVar("j"))) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("y1"),LVar("k"))) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("y1"),LVar("w3"))) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("y1"),LVar("jl"))) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("z"),LVar("f"))) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("x"),LVar("d56"))) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("z"),LVar("jlo"))) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("new_z"),LVar("new_mk"))) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("new_z"),LVar("new_mk2"))) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("z32"),LVar("f90"))) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("z32"),LVar("f99"))) test_unif_eq; 
   and_atomic_affect (Pointsto(PVar("z32"),LVar("C90"))) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("z32"),LVar("C99"))) test_unif_eq;
   add_alloc_cell (LVar("f90"))  test_unif_eq;
   add_alloc_cell (LVar("w3"))  test_unif_eq;
   add_alloc_cell (LVar("C99"))  test_unif_eq;
 (*  let aff_y1 = Hashtbl.find test_unif_eq.pure.affectations (PVar("y1")) in
   let aff_z = Hashtbl.find test_unif_eq.pure.affectations (PVar("z")) in
   let list_eq = ( unify_eq aff_y1 ) @ ( unify_eq aff_z) in
   print_eqlist form  list_eq;*)

     let all_theories = (Hashtbl.fold all_aff_fold_to_theory test_unif_eq.pure.affectations []) in
       Format.fprintf form  "List of equations of all_theories : \n";
       print_eqlist form all_theories ;
     
 
     let part = eqlist_to_partition all_theories in
       pprint_partition form part;
       Format.fprintf form "\n %!";
       let subst_test = subst_from_partition part in
       pprint_subst form subst_test;
       Format.fprintf  form "%!" ;
     
       subst_against_ssl subst_test test_unif_eq;

       Ssl.pprint_ssl_formula form  test_unif_eq;
       Format.fprintf  form "%!" ;

       Format.fprintf form " \n *********** test of normization *************** \n %!";
        let test_unif_eq = Ssl.create_ssl_f () in
   and_atomic_affect (Pointsto(PVar("y1"),LVar("l3"))) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("y1"),LVar("j"))) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("y1"),LVar("k"))) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("y1"),LVar("w3"))) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("y1"),LVar("jl"))) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("z"),LVar("f"))) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("x"),LVar("d56"))) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("z"),LVar("jlo"))) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("new_z"),LVar("new_mk"))) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("new_z"),LVar("new_mk2"))) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("z32"),LVar("f90"))) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("z32"),LVar("f99"))) test_unif_eq; 
   and_atomic_affect (Pointsto(PVar("z32"),LVar("C90"))) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("z32"),LVar("C99"))) test_unif_eq;
   add_alloc_cell (LVar("f90"))  test_unif_eq;
   add_alloc_cell (LVar("w3"))  test_unif_eq;
   add_alloc_cell (LVar("C99"))  test_unif_eq;
   add_quant_var (LVar("C99")) test_unif_eq;
   add_quant_var (LVar("Must_appear_in_qlist")) test_unif_eq;
   and_atomic_affect (Pointsto(PVar("Pointstoexists"),LVar("Must_appear_in_qlist") )) test_unif_eq;
  (*  and_atomic_affect (Pointsto(PVar("Pointstoexists"),LVar("free_varloc") )) test_unif_eq; *)
   Format.fprintf form "\n Equation to be normalized \n ";
   Ssl.pprint_ssl_formula form test_unif_eq;
   Format.fprintf form " \n Equation in normal form \n";
   normalize_ssl test_unif_eq;   
   Ssl.pprint_ssl_formula form  test_unif_eq;
   Format.fprintf  form "\n%!";
   begin
     if (sat_ssl test_unif_eq ) then 
       Format.fprintf form " \n Formula is SAT \n %!"
     else
       Format.fprintf form " \n Formula is UNSAT \n %!" 
   end;
   
   Format.fprintf  form " Testing garbageness \n %!";
   begin
     if garbage_ssl test_unif_eq then
        Format.fprintf form " \n Formula contains garbage \n %!"
     else
       Format.fprintf form " \n Formula contains no garbage \n %!"   
   end;

   add_alloc_cell (LVar("Unpointed_lvar"))  test_unif_eq;
    Format.fprintf  form " Testing garbageness \n %!";
   begin
     if garbage_ssl test_unif_eq then
        Format.fprintf form " \n Formula contains garbage \n %!"
     else
       Format.fprintf form " \n Formula contains no garbage \n %!"   
   end;

   let phi_g = create_ssl_f () in
   let phi_d = create_ssl_f () in
     and_atomic_affect (Pointsto(PVar("x"),LVar("l1"))) phi_g;
     and_atomic_affect (Pointsto(PVar("y"),LVar("l1"))) phi_g;
     add_alloc_cell (LVar("l1")) phi_g;
     add_alloc_cell (LVar("l2")) phi_g;
     add_quant_var (LVar("l1")) phi_g;
     and_atomic_affect (Pointsto(PVar("x"),LVar("m1"))) phi_d;
     and_atomic_affect (Pointsto(PVar("y"),LVar("m1"))) phi_d;
     add_alloc_cell (LVar("l1")) phi_d;
     add_alloc_cell (LVar("m1")) phi_d;
     add_quant_var (LVar("m1")) phi_d;
     let entp = {left = phi_g; right = phi_d ;} in
     Format.fprintf form "********* Entailement problem ********* \n";
        pprint_entailproblem form entp;
       entail_r4 None entp;
       Format.fprintf form " ************** Entailement problem afer r_4 *****\n";
       pprint_entailproblem form entp;
       
       let phi_g = create_ssl_f () in
       let phi_d = create_ssl_f () in
and_atomic_affect (Pointsto(PVar("x"),LVar("l1"))) phi_g;
       and_atomic_affect (Pointsto(PVar("y"),LVar("l1"))) phi_g;
       add_alloc_cell (LVar("l1")) phi_g;
       add_alloc_cell (LVar("l2")) phi_g;
       add_alloc_cell (LVar("Garbage_1")) phi_g;
       add_alloc_cell (LVar("Garbage_2")) phi_d;
       add_alloc_cell (LVar("Garbage_3")) phi_g;
       add_alloc_cell (LVar("Garbage_3")) phi_d;
       add_quant_var (LVar("l1")) phi_g;
       and_atomic_affect (Pointsto(PVar("x"),LVar("m1"))) phi_d;
       and_atomic_affect (Pointsto(PVar("y"),LVar("m1"))) phi_d;
       add_alloc_cell (LVar("l1")) phi_d;
       add_alloc_cell (LVar("m1")) phi_d;
       add_quant_var (LVar("m1")) phi_d;
       let entp = {left = phi_g; right = phi_d ;} in
       Format.fprintf form "********* Entailement problem ********* \n";
       pprint_entailproblem form entp;
       entail_r2 entp;
       Format.fprintf form " ************** Entailement problem afer r_2 *****\n";
       pprint_entailproblem form entp;
       let phi_g = create_ssl_f () in
       let phi_d = create_ssl_f () in
       and_atomic_affect (Pointsto(PVar("x"),LVar("l1"))) phi_g;
       and_atomic_affect (Pointsto(PVar("x"),LVar("l1"))) phi_d;
       add_alloc_cell (LVar("l1")) phi_g;
       add_alloc_cell (LVar("l2")) phi_g;
       add_alloc_cell (LVar("Garbage_1")) phi_g;
       add_alloc_cell (LVar("Garbage_2")) phi_d;
        add_alloc_cell (LVar("Garbage_3")) phi_g;
       add_alloc_cell (LVar("Garbage_3")) phi_d;
       add_quant_var (LVar("l1")) phi_g;
       and_atomic_affect (Pointsto(PVar("x"),LVar("m1"))) phi_d;
       and_atomic_affect (Pointsto(PVar("y"),LVar("m1"))) phi_d;
       add_alloc_cell (LVar("l1")) phi_d;
       add_alloc_cell (LVar("m1")) phi_d;
       add_quant_var (LVar("m1")) phi_d;
       let entp = {left = phi_g; right = phi_d ;} in
       Format.fprintf form "********* Entailement problem ********* \n";
       pprint_entailproblem form entp;
       entail_r1 entp;
       Format.fprintf form " ************** Entailement problem afer r_1 *****\n";
       pprint_entailproblem form entp ;
	 
    let phi_g = create_ssl_f () in
       let phi_d = create_ssl_f () in
and_atomic_affect (Pointsto(PVar("x"),LVar("l1"))) phi_g;
       and_atomic_affect (Pointsto(PVar("y"),LVar("l1"))) phi_g;
       add_alloc_cell (LVar("l1")) phi_g;
       add_alloc_cell (LVar("l2")) phi_g;
       add_alloc_cell (LVar("Garbage_1")) phi_g;
       add_alloc_cell (LVar("Garbage_1")) phi_d;
       add_alloc_cell (LVar("Garbage_2")) phi_g;
       add_alloc_cell (LVar("Garbage_2")) phi_d;
       add_alloc_cell (LVar("Garbage_3")) phi_g;
       add_alloc_cell (LVar("Garbage_3")) phi_d;
       add_quant_var (LVar("l1")) phi_g;
       and_atomic_affect (Pointsto(PVar("x"),LVar("m1"))) phi_d;
       and_atomic_affect (Pointsto(PVar("y"),LVar("m1"))) phi_d;
       add_alloc_cell (LVar("l1")) phi_d;
       add_alloc_cell (LVar("m1")) phi_d;
       add_quant_var (LVar("m1")) phi_d;
       add_quant_var (LVar("Garbage_1")) phi_g;
       add_quant_var (LVar("Garbage_1")) phi_d;
       add_quant_var (LVar("Garbage_2")) phi_g;
       add_quant_var (LVar("Garbage_2")) phi_d;
       add_quant_var (LVar("Garbage_3")) phi_d;
       
       let entp = {left = phi_g; right = phi_d ;} in
       Format.fprintf form "********* Entailement problem ********* \n";
       pprint_entailproblem form entp;
       entail_r6 entp;
       Format.fprintf form " ************** Entailement problem afer r_6 *****\n";
       pprint_entailproblem form entp;

       	 
    let phi_g = create_ssl_f () in
       let phi_d = create_ssl_f () in
and_atomic_affect (Pointsto(PVar("x"),LVar("l1"))) phi_g;
       and_atomic_affect (Pointsto(PVar("y"),LVar("l1"))) phi_g;
       add_alloc_cell (LVar("l1")) phi_g;
       add_alloc_cell (LVar("l2")) phi_g;
       add_alloc_cell (LVar("Garbage_1")) phi_g;
       add_alloc_cell (LVar("Garbage_1")) phi_d;
       add_alloc_cell (LVar("Garbage_2")) phi_g;
       add_alloc_cell (LVar("Garbage_2")) phi_d;
       add_alloc_cell (LVar("Garbage_3")) phi_g;
       add_alloc_cell (LVar("Garbage_3")) phi_d;
       add_quant_var (LVar("l1")) phi_g;
       and_atomic_affect (Pointsto(PVar("x"),LVar("m1"))) phi_d;
       and_atomic_affect (Pointsto(PVar("y"),LVar("m1"))) phi_d;
       add_alloc_cell (LVar("l1")) phi_d;
       
       add_quant_var (LVar("m1")) phi_d;
       add_quant_var  (LVar("mhohljkh")) phi_d;
       add_quant_var (LVar("Garbage_1")) phi_g;
       add_quant_var (LVar("Garbage_1")) phi_d;
       add_quant_var (LVar("Garbage_2")) phi_g;
       add_quant_var (LVar("Garbage_2")) phi_d;
       add_quant_var (LVar("Garbage_3")) phi_d;
       add_quant_var (LVar("Garbage_3")) phi_g;
       let entp = {left = phi_g; right = phi_d ;} in
       Format.fprintf form "********* Entailement problem ********* \n";
       pprint_entailproblem form entp;
       let biabduct_res = biabduction entp in
       Format.fprintf form "********* Entailement problem After biabduction ********* \n";
        Format.fprintf form "********* Enunciate after renaming ********* \n";
       pprint_entailproblem form biabduct_res.enunciate;
        Format.fprintf form "********* Frame and antiframe ********* \n";
       pprint_entailproblem form biabduct_res.frame_antiframe;
        let phi_g = create_ssl_f () in
       let phi_d = create_ssl_f () in
       and_atomic_affect (Pointsto(PVar("x"),LVar("l1"))) phi_g;
       and_atomic_affect (Pointsto(PVar("y"),LVar("l2"))) phi_g;
       add_alloc_cell (LVar("l1")) phi_g;
       add_alloc_cell (LVar("l2")) phi_g;
       add_quant_var (LVar("l1")) phi_g;
       and_atomic_affect (Pointsto(PVar("x"),LVar("m1"))) phi_d;
       and_atomic_affect (Pointsto(PVar("y"),LVar("l1"))) phi_d;
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

       let etpf = { 
	 left = (star_sep biabduct_res.enunciate.left biabduct_res.frame_antiframe.right ) ;
	 right = (star_sep biabduct_res.enunciate.right biabduct_res.frame_antiframe.left ) 
       } in
	 pprint_entailproblem form etpf
	 



       
       
       


let () = main ()
