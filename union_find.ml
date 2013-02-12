open Ssl_types
open Ssl_types.SSL_lex
open Ssl
open Hashtbl

(** This file contains the current implementations of the
"union find" algorithm used to compute the representant 
of equivalences classes defined by a set of equalities 

for questions or comment, write to florent-dot-garnier!at!imag^dot^fr

*)

exception FVar_found

type eqclass = {
  mutable repres : locvar ;      (*Member representing the class*)
  members : ( locvar , unit ) t; (*All members but the representant*)
}
  
type partition = Partition of (locvar , eqclass ) t
(** Key of partition corresponds to the greatest key of 
the eq class. partition encodes a forest.
*)

exception Element_not_found 
exception Non_membership (* An equivalence class, or an equivalence
			    class referenced by its representant does 
			    not belong to a partition.*)

(** returns true if one locvar of cl is a f.v. of sslf, false otherwise *)

let eqclass_exists_free_var  (cl : eqclass) (sslf : ssl_formula) =
  let eqclass_iterator lvar () =
    if (Hashtbl.mem sslf.quant_vars lvar) then ()
    else raise FVar_found 
  in
    try	  
      Hashtbl.iter eqclass_iterator cl.members; false
    with
	FVar_found -> true


(** Is lvar the representant of an equivalence class of part ?*)
let is_rep_of_a_class (lvar : locvar ) ( part : partition ) =
  match part with
      Partition ( table ) -> Hashtbl.mem table lvar 

(** Finds of an element returns the key of the class of this element
or an exception if this element does'nt belong to  *)
let find_repr (lvar : locvar )( part : partition ) =
  let ret = ref (LVar("")) in 
  let eqclass_iterator ( key  :  locvar) ( iterande : locvar ) ( eqc : eqclass) =
    if (Hashtbl.mem eqc.members key) ==true 
	  then ret := iterande
	  else ()
  in
  match part with 
      Partition (table ) ->
	if ( Hashtbl.mem table lvar ) == true (* Case where the
						 query is a key*)
	then let eqcl = (Hashtbl.find table lvar) 
	     in  eqcl.repres                                  
	else  
	  begin
	  Hashtbl.iter (eqclass_iterator lvar ) table ; !ret
	  end

	  (** Return the valuet LVar("") if no equivalence
	  class has been found *)


(*  A refaire dans l'autre sens. Il faut trouver un representant d
'une classe d'equivalence vide ou par defaut *)

(** find_class raises  Element_not_found  if lvar is not an element
in the partition *)
let find_class (lvar : locvar ) ( part : partition ) =
  let repres = find_repr lvar part in
  match repres with 
      LVar("")-> {repres = LVar(""); members = Hashtbl.create 1 }
    | _ ->
      match part with 
	  Partition( table ) ->
	    Hashtbl.find table repres 
	      (* We get the whole class, hence this 
		 return value.*)


(** Merges two equivances classes of the partition part into a single one.
Copies all elements of eqmin in the class of eqmax, then removes eqmin
from the partition. One must ensure that eqmax and eqmin are both
member of part. The function union gurantee that while calling to union_wrt_order.*)
let merge_wrt_order (eqmax : eqclass ) (eqmin : eqclass ) (part : partition) =
  let copy_iterator lvar () =
    Hashtbl.add eqmax.members lvar ()
  in
  Hashtbl.iter copy_iterator eqmin.members;
  Hashtbl.add eqmax.members eqmin.repres ();
  match part with
      Partition(tablepart) ->
	Hashtbl.remove tablepart (eqmin.repres)

(** Merges two classes of the partition part, into a single one *)	
let merge_class (eq_1: eqclass) (eq_2: eqclass) (part : partition ) = 
 
  if  ((is_rep_of_a_class eq_1.repres part ) && (is_rep_of_a_class eq_2.repres part   ) ) then begin
    if ( Ssl.cmp_lex_lvar eq_1.repres eq_2.repres ) then 
      merge_wrt_order eq_1 eq_2 part
    else 
      merge_wrt_order eq_2 eq_1 part
  end
  else raise Non_membership

(** Merges the equivalence classes of each member of the equations,
if they are indeed distinct.*)
let merge_from_equality (equality : SSL_lex.eq )(part : partition ) =
  match equality with 
      Eqloc(l1,l2)->
	let classe1 = find_class l1 part in
	let classe2 = find_class l2 part in
	merge_class classe1 classe2 part
	  (** Et puis basta !*)




(** 
This fonctions performs the following operation :
If both members of an equation are not member of a 
partition, then one creates a new class that contains
those two elements.

If the greatest element belongs to a class and the
smallest doesn't then, one add both element to
this class.


If the smallest element belong to a class but the biggest
doesn't, then :

the biggest element of the equation becomes the representant
of the class, and the former representant is moved together 
with the other element of the class.

The last case corresponds to the fact that both elements
already belong to equivalence classe,
 In this case, one shall merge both classes, whenever those
two classes are different.
 
 the third parameter is required, because "part" is a hastable that
contains all equivalence class, which are indexed by their
representant. Any change of a representant of a class must
be propagated within this index. *)
let add_element_to_class ( lvar : SSL_lex.locvar )( ecl : eqclass )( part : partition) =
  if (( cmp_lex_lvar lvar  ecl.repres ) == true) 
  then
    match part with
	Partition ( table ) ->
	  (*try*)
	    let update_class = Hashtbl.find table ecl.repres in
	    Hashtbl.remove table update_class.repres ; (*removing
						       binding from
						       patition*)
	    
	    update_class.repres <- lvar ;
	    Hashtbl.add update_class.members ecl.repres ();
	    Hashtbl.add table  lvar update_class 
	 (* with
	      Element_not_found ->
	    | Non_membership -> *)	
	     
  else
    Hashtbl.add ecl.members lvar () 
  
(** Adds a new partition to the partition to the eqclass*)    
let add_class_to_partition (ecl : eqclass )( part : partition ) =
  match part with
      Partition ( table_part ) ->
	Hashtbl.add table_part ecl.repres ecl
  
  


(********************************************************)


(** Adds an equality and modifies the partition accordingly.*)
let add_eq_to_partition (part : partition) (equation : SSL_lex.eq) =
  let eqsort = ref equation in
  match equation with 
      Eqloc ( lg , ld ) ->
	begin
	  let lmax = ref lg in
	  let lmin = ref ld in
	  begin
	    if (( cmp_lex_lvar lg ld ) == false)
	    then  
	      begin
		eqsort := (Eqloc ( ld , lg ));
		lmax := ld; 
		lmin := lg
	      end
	    else ()
	  end;
	  let class_max  =  find_class  (!lmax) part  in
	  let class_min = find_class !lmin part  in
	  match class_max.repres , class_min.repres with 
	      (LVar(""), LVar("")) -> 
		let table_nclass = Hashtbl.create SSL_lex.size_hash in
		Hashtbl.add table_nclass !lmin ();
		let new_class = {
		  repres = !lmax;
		  members = table_nclass 
		} in
		add_class_to_partition new_class part
	    | (LVar(""), _ ) ->  add_element_to_class !lmax class_min part
	    | (_ , LVar("")) ->  add_element_to_class !lmin class_max part 
	    | ( _ , _ ) -> merge_wrt_order class_max class_min part
	end
	 
(** Creates a partition from a list of equations*)      
let eqlist_to_partition( eqlist : SSL_lex.eq list ) =
  let order_elem (s : SSL_lex.eq) =
    match s with 
	Eqloc (LVar (lg) , LVar (ld) ) ->  
	  if (SSL_lex.order_relation lg ld)!= true then
	    Eqloc (LVar (lg) , LVar (ld) ) 
	  else 
  	    Eqloc (LVar (lg) , LVar (ld) )
  in
  let part = Partition ( Hashtbl.create SSL_lex.size_hash ) in
  let ordered_list = List.map  order_elem eqlist in
  let create_part_iterator (s : SSL_lex.eq) =
    add_eq_to_partition part s
  in  
  List.iter create_part_iterator ordered_list;
  part
  
   
(** Prints an equation class into a string.*)
let eqclass_to_string (eq : eqclass) =
  let member_to_string (lvar: locvar ) () (res : string ) =
    match lvar with 
	LVar(vname) -> ( res^";"^vname)
  in
  match eq.repres with 
      LVar(rep_name) -> "Class of : ["^ rep_name ^"] : " ^( Hashtbl.fold member_to_string eq.members  "") 

(** Prints a partition into a string.*)
let part_to_string (part : partition ) =
  match part with 
      Partition(part_table) ->
	let part_fold lvar eq_c str =
	  match lvar with
	      LVar(cname) -> "Class_name: [ "^cname^" ] Eqclass: "^(eqclass_to_string eq_c )^"\n"^str
	in
	  ( " Partition : \n"^( Hashtbl.fold part_fold part_table "" ))

(** Pretty prints a partition into a formatter.*)
let pprint_partition (out : Format.formatter ) (part : partition) =
  match part with 
      Partition ( part_table ) ->
	let pmess = part_to_string part in
	let nb_classes =  Hashtbl.length part_table in
	  Format.fprintf out "Nombre de classes : %d \n " nb_classes;
	  Format.fprintf out  "%s" pmess;
	  Format.fprintf out "%!"

   

