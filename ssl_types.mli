module SSL_types_gen :
  functor
    (P : sig
           val order_relation : string -> string -> bool
           val equals_to : string -> string -> bool
         end) ->
    sig
      val size_hash : int
      val order_relation : string -> string -> bool
      val equals_to : string -> string -> bool
      type ptvar = PVar of string
      type locvar = LVar of string
      type eq = Eqloc of locvar * locvar
      type affect = Pointsto of ptvar * locvar
      type affectnil = Pointsnil of ptvar
      type pure_formula = {
        mutable equations : eq list;
        affectations : (ptvar, (locvar, unit) Hashtbl.t) Hashtbl.t;
        ptnil : (ptvar, unit) Hashtbl.t;
      }
      type space_formula = Space of (locvar, int) Hashtbl.t | Top_heap
      type ssl_formula = {
        quant_vars : (locvar, unit) Hashtbl.t;
        pure : pure_formula;
        mutable space : space_formula;
      }
    end
module SSL_lex :
  sig
    val size_hash : int
    val order_relation : string -> string -> bool
    val equals_to : string -> string -> bool
    type ptvar = PVar of string
    type locvar = LVar of string
    type eq = Eqloc of locvar * locvar
    type affect = Pointsto of ptvar * locvar
    type affectnil = Pointsnil of ptvar
    type pure_formula = {
      mutable equations : eq list;
      affectations : (ptvar, (locvar, unit) Hashtbl.t) Hashtbl.t;
      ptnil : (ptvar, unit) Hashtbl.t;
    }
    type space_formula = Space of (locvar, int) Hashtbl.t | Top_heap
    type ssl_formula = {
      quant_vars : (locvar, unit) Hashtbl.t;
      pure : pure_formula;
      mutable space : space_formula;
    }
  end
exception Top_heap_exception
exception Lvar_found
exception Get_a_locvar of SSL_lex.locvar
exception No_such_pvar_in_ssl_formula of string
exception Contains_no_pvar
exception Loc_is_nil
exception Loc_is_a_constant of int64
exception No_pvar_in_param_list
