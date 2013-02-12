(**


SSL library, ssl_normalization. 

Those functions are defined to rewrite any formula of the
SSL abstract domain in a (unique) normal form.

Written by Florent Garnier, at Verimag Labs  2012 
Contact florent dot garnier at gmail dot com for  further informations.

This files is released under the terms of the LGPL v2.1 Licence.

 
This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 2.1 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor,
 Boston, MA  02110-1301  USA

*)



val var_elim : Ssl_types.SSL_lex.ssl_formula -> unit


val theories_cleanup : Ssl_types.SSL_lex.ssl_formula -> unit

val q_elim : Ssl_types.SSL_lex.ssl_formula -> Union_find.partition -> unit

val normalize_ssl : Ssl_types.SSL_lex.ssl_formula -> unit
