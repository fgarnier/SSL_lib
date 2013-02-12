(*
This file belongs to the Simple Separation Logic library.
The SSL implements an abstract domain used to reason with shallow
propertues of the memory.


The SSL lib is a part of the Frama-c FLATA-C plugin, developped
in the VERIMAG Laboratory.

Written by Florent Garnier, 2012-2013.

Released under the terms of the LGPL v2.1 Licence.

The functions below implements decision procedures that allow
to answer decision problems.
*)



exception SSL_unsat
exception No_locvars_left
exception Lvar_present
exception Not_pointed
val is_rel_in :
  Ssl_types.SSL_lex.ptvar ->
  Ssl_types.SSL_lex.locvar -> Ssl_types.SSL_lex.ssl_formula -> bool
val free_var :
  Ssl_types.SSL_lex.ssl_formula -> Ssl_types.SSL_lex.locvar -> bool

(** Does a model A exists such that ssl_formula is satisfiable under A ?*)
val sat_ssl : Ssl_types.SSL_lex.ssl_formula -> bool


val is_locvar_pointed_at :
  Ssl_types.SSL_lex.locvar -> Ssl_types.SSL_lex.pure_formula -> bool

(** Does a SSL formula contains an allocated memory cell that is
not reachable using the stack pointers ? *)
val garbage_ssl : Ssl_types.SSL_lex.ssl_formula -> bool
