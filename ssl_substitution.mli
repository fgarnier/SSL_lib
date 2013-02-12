(*
This file belongs to the Simple Separation Logic library.
The SSL implements an abstract domain used to reason with shallow
propertues of the memory.


The SSL lib is a part of the Frama-c FLATA-C plugin, developped
in the VERIMAG Laboratory.

Written by Florent Garnier, 2012-2013.

Released under the terms of the LGPL v2.1 Licence.

Definition of a type describing substitions between local variables,
and functions that allow to apply such substition upon SSL formuli.

*)


type loc_subst =
    Subst of (Ssl_types.SSL_lex.locvar, Ssl_types.SSL_lex.locvar) Hashtbl.t

val subst_id : loc_subst

(*
val eq_class_inversor :
  Ssl_types.SSL_lex.locvar ->
  Ssl_types.SSL_lex.locvar ->
  unit ->
  (Ssl_types.SSL_lex.locvar, Ssl_types.SSL_lex.locvar) Hashtbl.t ->
  (Ssl_types.SSL_lex.locvar, Ssl_types.SSL_lex.locvar) Hashtbl.t
*)

(** Takes as input a partition of the local variables, itself computed
from a set of equations. Returns the subtition that associates each
variable to the representant of its class --i.e. the least element
of the class w.r.t. the order relation on the local variable used to
define the partition.*)
val subst_from_partition : Union_find.partition -> loc_subst
(*
val subst_against_quant_vars :
  loc_subst -> (Ssl_types.SSL_lex.locvar, unit) Hashtbl.t -> unit

val map_subst_list_eq :
  loc_subst -> Ssl_types.SSL_lex.eq -> Ssl_types.SSL_lex.eq
*)

(*
val subst_against_eqlist :
  loc_subst -> Ssl_types.SSL_lex.eq list -> Ssl_types.SSL_lex.eq list

val subst_against_affectation :
  loc_subst ->
  (Ssl_types.SSL_lex.ptvar, (Ssl_types.SSL_lex.locvar, unit) Hashtbl.t)
  Hashtbl.t -> unit

val subst_against_space :
  loc_subst -> Ssl_types.SSL_lex.space_formula -> unit
*)

(** Replace every instance of local variable of a SSL formula with
its class reprensentant.*)
val subst_against_ssl : loc_subst -> Ssl_types.SSL_lex.ssl_formula -> unit

(** Computes the composition of two substitution*)
val compose_subst : loc_subst -> loc_subst -> loc_subst




(*
val subst_var_qvars_nil :
  Ssl_types.SSL_lex.locvar -> Ssl_types.SSL_lex.ssl_formula -> unit

val subst_lvar_to_nil_in_affect :
  Ssl_types.SSL_lex.locvar -> Ssl_types.SSL_lex.ssl_formula -> unit

val subst_lvar_to_nil_in_heap :
  Ssl_types.SSL_lex.locvar -> Ssl_types.SSL_lex.ssl_formula -> unit
*)

(** Substitutes a local variable by nil in a SSL formula*)
val subst_to_nil_upon_sslf :
  Ssl_types.SSL_lex.locvar -> Ssl_types.SSL_lex.ssl_formula -> unit
