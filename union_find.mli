(*
This file belongs to the Simple Separation Logic library.
The SSL implements an abstract domain used to reason with shallow
propertues of the memory.


The SSL lib is a part of the Frama-c FLATA-C plugin, developped
in the VERIMAG Laboratory.

Written by Florent Garnier, 2012-2013.

Released under the terms of the LGPL v2.1 Licence.

*)


exception FVar_found

type eqclass = {
  mutable repres : Ssl_types.SSL_lex.locvar;
  members : (Ssl_types.SSL_lex.locvar, unit) Hashtbl.t;
}

type partition = Partition of (Ssl_types.SSL_lex.locvar, eqclass) Hashtbl.t

exception Element_not_found
exception Non_membership

val eqclass_exists_free_var :
  eqclass -> Ssl_types.SSL_lex.ssl_formula -> bool

val is_rep_of_a_class : Ssl_types.SSL_lex.locvar -> partition -> bool

val find_repr :
  Ssl_types.SSL_lex.locvar -> partition -> Ssl_types.SSL_lex.locvar

val find_class : Ssl_types.SSL_lex.locvar -> partition -> eqclass

val merge_wrt_order : eqclass -> eqclass -> partition -> unit

val merge_class : eqclass -> eqclass -> partition -> unit

val merge_from_equality : Ssl_types.SSL_lex.eq -> partition -> unit

val add_element_to_class :
  Ssl_types.SSL_lex.locvar -> eqclass -> partition -> unit

val add_class_to_partition : eqclass -> partition -> unit

val add_eq_to_partition : partition -> Ssl_types.SSL_lex.eq -> unit

val eqlist_to_partition : Ssl_types.SSL_lex.eq list -> partition

val eqclass_to_string : eqclass -> string

val part_to_string : partition -> string

val pprint_partition : Format.formatter -> partition -> unit
