SOURCE_FILES := ssl_types.ml ssl.ml union_find.ml ssl_substitution.ml\
		ssl_printers.ml ssl_normalization.ml ssl_entailement.ml\
		ssl_decision.ml ssl_biabduction.ml
	 
INCLUDE_DIR := ./include
OCAMLDOC := ocamldoc
DOCEXPORTDIR := ./api
INCLUDEDIR := ./include
LIBDIR := ./lib
BINDIR := ./bin
LIBTARGETNAME := libocamlssl.cma
XLIBTARGETNAME := libxocamlssl.cmxa

CFLAGS := -annot -c
DOCFLAGS := -html -d $(DOCEXPORTDIR) *.ml *.mli

OBJECTS := ssl_types.cmo ssl.cmo union_find.cmo ssl_substitution.cmo\
	ssl_pprinters.cmo ssl_normalization.cmo ssl_entailement.cmo \
	ssl_decision.cmo ssl_biabduction.cmo 
		

XOBJECTS := ssl_types.cmx ssl.cmx union_find.cmx ssl_substitution.cmx\
	ssl_pprinters.cmx ssl_normalization.cmx ssl_entailement.cmx \
	ssl_decision.cmx ssl_biabduction.cmx 


%.cmo : %.ml
	@echo  "Compiling"  $<
	@ocamlc ${CFLAGS}  $< -o $@ ${TYPES_INCLUDES}

%.cmi : %.mli
	@echo  "Compiling interface " $<
	@ocamlc ${CFLAGS}  $< -o $@ $(TYPES_INCLUDES)

%.cmx : %.ml
	@echo  "OPT Compiling"  $<
	@ocamlopt ${CFLAGS}  $< -o $@ ${TYPES_INCLUDES}


ssl_lib : $(OBJECTS)
	@echo "Building" $(LIBTARGETNAME)
	@ocamlc -o $(LIBTARGETNAME) -a $(OBJECTS)
	
ssl_xlib : $(XOBJECTS)
	@echo "Building"  $(XLIBTARGETNAME)
	@ocamlopt -o $(XLIBTARGETNAME) -a $(XOBJECTS)


doc_html : $(OBJECTS)
	@echo "Generating HTML API"
	@$(OCAMLDOC) $(DOCFLAGS)

sort_include_lib :
	@echo "Moving libs to lib/ and copy *.mli in include/" 
	@cp *.mli ${INCLUDE_DIR}
	@mv *.cma *.cmxa *.a ${LIBDIR}

all : .depend ssl_lib ssl_xlib doc_html sort_include_lib

clean :
	rm *.o *.cmo *.cmx *.cma *.cmxa *.cmi *.annot

include .depend

.depend : $(LIBSOURCES)
	ocamldep *.ml *.mli > .depend
