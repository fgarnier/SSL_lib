(*
This file belongs to the Simple Separation Logic library.
The SSL implements an abstract domain used to reason with shallow
propertues of the memory.


The SSL lib is a part of the Frama-c FLATA-C plugin, developped
in the VERIMAG Laboratory.

Written by Florent Garnier, 2012-2013.

Released under the terms of the LGPL v2.1 Licence.

The biabduction problem is fully detailed in the associated 
technical report, please have a look there first.

*)


type biabduct_sol = {
  enunciate : Ssl_entailement.entail_problem;
  frame_antiframe : Ssl_entailement.entail_problem;
}

(*
val fold_substs :
  Ssl_types.SSL_lex.locvar -> Ssl_types.SSL_lex.locvar -> string -> string
val subst_to_string : Ssl_substitution.loc_subst -> string
*)
val biabduction : Ssl_entailement.entail_problem -> biabduct_sol
