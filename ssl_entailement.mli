exception No_more_vars

type entail_problem = {
  left : Ssl_types.SSL_lex.ssl_formula;
  right : Ssl_types.SSL_lex.ssl_formula;
}

type entail_subst = {
  lsubst : Ssl_substitution.loc_subst;
  rsubst : Ssl_substitution.loc_subst;
}


type fresh_loc_var = FLVar of string * int


val entail_subst_id : entail_subst

val flvar_to_locvar : fresh_loc_var -> Ssl_types.SSL_lex.locvar

val fresh_flvar : fresh_loc_var -> fresh_loc_var

val garbage_exists_lvar_heap :
  Ssl_types.SSL_lex.ssl_formula -> (Ssl_types.SSL_lex.locvar, unit) Hashtbl.t

val fresh_locvar_name_from_etp : entail_problem -> fresh_loc_var

(*
val varname_folder :
  Ssl_types.SSL_lex.locvar ->
  unit -> Ssl_types.SSL_lex.locvar -> Ssl_types.SSL_lex.locvar
*)

(** The functions below implement the set of reductions rules that allow
to determine wheter an entailement problem is satisfiable or not.*)
val entail_r1 : entail_problem -> unit
val entail_r1_nil : entail_problem -> unit
val entail_r3 : entail_problem -> unit
val entail_r3_nil : entail_problem -> unit
val entail_r4 : entail_subst ref option -> entail_problem -> unit
val entail_r5 : entail_problem -> unit
val entail_ptnil : entail_problem -> unit
val entail_r2 : entail_problem -> unit
val entail_r6 : entail_problem -> unit


(** Reduces an entailement problem *)
val ssl_entailement : entail_problem -> unit

val pprint_entailement_problem : entail_problem -> string

(** Reduces an entailement problem and check wheter its satisfiable
or not.*)
val does_entail : entail_problem -> bool

val accept_new_abstraction : entail_problem -> bool

val entails_abstraction_adder : entail_problem -> bool
