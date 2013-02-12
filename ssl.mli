(*
This file belongs to the Simple Separation Logic library.
The SSL implements an abstract domain used to reason with shallow
propertues of the memory.


The SSL lib is a part of the Frama-c FLATA-C plugin, developped
in the VERIMAG Laboratory.

Written by Florent Garnier, 2012-2013.

Released under the terms of the LGPL v2.1 Licence.

The file ssl.mli defines the interface of the most basic functions
used to handle SSL formuli : Create a formuly, adding/removing
a pointer/location variable, a cell on a heap, conjunction 
of two SSL formuli etc ...


Definition of a type describing substitions between local variables,
and functions that allow to apply such substition upon SSL formuli.

*)



val cmp_lex_lvar :
  Ssl_types.SSL_lex.locvar -> Ssl_types.SSL_lex.locvar -> bool
(*
val create_pure_f : unit -> Ssl_types.SSL_lex.pure_formula
val create_space_f : unit -> Ssl_types.SSL_lex.space_formula
*)
val create_ssl_f : unit -> Ssl_types.SSL_lex.ssl_formula
(*
val orient_eq : Ssl_types.SSL_lex.eq -> Ssl_types.SSL_lex.eq
val orient_eqlist : Ssl_types.SSL_lex.eq list -> Ssl_types.SSL_lex.eq list
val fold_max :
  Ssl_types.SSL_lex.locvar ->
  unit -> Ssl_types.SSL_lex.locvar -> Ssl_types.SSL_lex.locvar
val biggest_loc_var :
  (Ssl_types.SSL_lex.locvar, unit) Hashtbl.t -> Ssl_types.SSL_lex.locvar
val extract_eq_from_hashtbl :
  Ssl_types.SSL_lex.eq list ref ->
  Ssl_types.SSL_lex.locvar -> Ssl_types.SSL_lex.locvar -> unit -> unit
*)


val unify_eq :
  (Ssl_types.SSL_lex.locvar, unit) Hashtbl.t -> Ssl_types.SSL_lex.eq list

(*val _del_tautologies :
  Ssl_types.SSL_lex.eq list ->
  Ssl_types.SSL_lex.eq list -> Ssl_types.SSL_lex.eq list
*)
val del_tautologies : Ssl_types.SSL_lex.eq list -> Ssl_types.SSL_lex.eq list

val pick_first_lvar :
  (Ssl_types.SSL_lex.locvar, unit) Hashtbl.t -> Ssl_types.SSL_lex.locvar

val subst_loc :
  Ssl_types.SSL_lex.locvar ->
  Ssl_types.SSL_lex.locvar -> Ssl_types.SSL_lex.eq -> Ssl_types.SSL_lex.eq

val subst_eqlist :
  Ssl_types.SSL_lex.locvar ->
  Ssl_types.SSL_lex.locvar ->
  Ssl_types.SSL_lex.eq list -> Ssl_types.SSL_lex.eq list 

(*val subst_loc_affect_ite :
  (Ssl_types.SSL_lex.locvar, unit) Hashtbl.t ->
  Ssl_types.SSL_lex.locvar ->
  Ssl_types.SSL_lex.locvar -> Ssl_types.SSL_lex.locvar -> unit -> unit
val inter_tabl_ptvar_loc :
  Ssl_types.SSL_lex.locvar ->
  Ssl_types.SSL_lex.locvar ->
  Ssl_types.SSL_lex.ptvar ->
  (Ssl_types.SSL_lex.locvar, unit) Hashtbl.t -> unit
val subst_lvar_affect :
  Ssl_types.SSL_lex.locvar ->
  Ssl_types.SSL_lex.locvar ->
  (Ssl_types.SSL_lex.ptvar, (Ssl_types.SSL_lex.locvar, unit) Hashtbl.t)
  Hashtbl.t -> unit
val print_qvars_iterator :
  Format.formatter -> bool -> Ssl_types.SSL_lex.locvar -> unit -> unit
val print_exist_vars :
  Format.formatter -> (Ssl_types.SSL_lex.locvar, unit) Hashtbl.t -> unit
val print_eq_iterator :
  Format.formatter -> bool -> Ssl_types.SSL_lex.eq -> unit
val print_eqlist : Format.formatter -> Ssl_types.SSL_lex.eq list -> unit
val print_pointstonil :
  Format.formatter -> (Ssl_types.SSL_lex.ptvar, unit) Hashtbl.t -> unit
val print_affect_iter2 :
  Format.formatter ->
  Ssl_types.SSL_lex.ptvar -> Ssl_types.SSL_lex.locvar -> unit -> unit
val print_affect_iter1 :
  Format.formatter ->
  Ssl_types.SSL_lex.ptvar ->
  (Ssl_types.SSL_lex.locvar, unit) Hashtbl.t -> unit
val print_affect :
  Format.formatter ->
  (Ssl_types.SSL_lex.ptvar, (Ssl_types.SSL_lex.locvar, unit) Hashtbl.t)
  Hashtbl.t -> unit
val print_space_iter :
  Format.formatter -> bool -> Ssl_types.SSL_lex.locvar -> int -> unit
val print_space : Format.formatter -> Ssl_types.SSL_lex.space_formula -> unit*)


(*
val print_pure_formula :
  Format.formatter -> Ssl_types.SSL_lex.pure_formula -> unit
*)


(** Pretty prints a SSL formula.*)
  
val pprint_ssl_formula :
  Format.formatter -> Ssl_types.SSL_lex.ssl_formula -> unit


val add_quant_var :
  Ssl_types.SSL_lex.locvar -> Ssl_types.SSL_lex.ssl_formula -> unit

val and_atomic_eq :
  Ssl_types.SSL_lex.eq -> Ssl_types.SSL_lex.ssl_formula -> unit

val and_atomic_affect :
  Ssl_types.SSL_lex.affect -> Ssl_types.SSL_lex.ssl_formula -> unit

val change_affect_var :
  Ssl_types.SSL_lex.affect -> Ssl_types.SSL_lex.ssl_formula -> unit
  
val and_atomic_ptnil :
  Ssl_types.SSL_lex.affectnil -> Ssl_types.SSL_lex.ssl_formula -> unit
  
val add_alloc_occurences_space :
  Ssl_types.SSL_lex.locvar -> int -> Ssl_types.SSL_lex.space_formula -> unit
  

val add_alloc_cell :
  Ssl_types.SSL_lex.locvar -> Ssl_types.SSL_lex.ssl_formula -> unit

val add_alloc_cell_occ :
  Ssl_types.SSL_lex.locvar -> int -> Ssl_types.SSL_lex.ssl_formula -> unit
(*
val and_pure_ssl :
  Ssl_types.SSL_lex.ssl_formula ->
  Ssl_types.SSL_lex.ssl_formula -> Ssl_types.SSL_lex.ssl_formula

val star_sep :
  Ssl_types.SSL_lex.ssl_formula ->
  Ssl_types.SSL_lex.ssl_formula -> Ssl_types.SSL_lex.ssl_formula
  *)

(*
val cmp_eq : Ssl_types.SSL_lex.eq -> Ssl_types.SSL_lex.eq -> int
*)
val pure_contains_locvar :
  Ssl_types.SSL_lex.locvar -> Ssl_types.SSL_lex.pure_formula -> bool

val space_contains_locvar :
  Ssl_types.SSL_lex.locvar -> Ssl_types.SSL_lex.space_formula -> bool

val is_exists_quantified :
  Ssl_types.SSL_lex.locvar -> Ssl_types.SSL_lex.ssl_formula -> bool

val is_allocated :
  Ssl_types.SSL_lex.locvar -> Ssl_types.SSL_lex.ssl_formula -> bool

val ssl_contains_locvar :
  Ssl_types.SSL_lex.locvar -> Ssl_types.SSL_lex.ssl_formula -> bool

(*
val copy_space_formula :
  Ssl_types.SSL_lex.space_formula -> Ssl_types.SSL_lex.space_formula
*)

(** SSL formula are represented thanks to mutable data structures,
especially hash table. The copy function creates a new instance
of the formula given in parametter.*)
val copy : Ssl_types.SSL_lex.ssl_formula -> Ssl_types.SSL_lex.ssl_formula


val get_name_of_ptvar : Ssl_types.SSL_lex.ptvar -> string
val get_name_of_locvar : Ssl_types.SSL_lex.locvar -> string
val get_ptr_affectation :
  Ssl_types.SSL_lex.ssl_formula ->
  Ssl_types.SSL_lex.ptvar -> Ssl_types.SSL_lex.locvar

(** Set the heap shape of a SSL formula as heap, meaning that it
corresponds to a broken state.*)
val set_heap_to_top : Ssl_types.SSL_lex.ssl_formula -> unit

(** Tries to remove the segment pointed by the local variable given
as first parameter.
Pure(...) | Alloc(l1)    

try_remove_sebment l1 (Pure(...) | Alloc(l1)*Q) -> (Pure(...)|Q)
try_remove_sebment l1 (Pure(...) | Q ) -> (Pure(...)|Top) if Q
contains not predicate Alloc(l1)
*)
val try_remove_segment :
  Ssl_types.SSL_lex.locvar -> Ssl_types.SSL_lex.ssl_formula -> unit
