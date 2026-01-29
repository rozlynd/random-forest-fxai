COQ_DIR = coq
OCAML_DIR = ocaml

all: coq
	dune build --root=$(OCAML_DIR)

.PHONY: clean clean-extract coq coq-extract

coq:
	$(MAKE) -C $(COQ_DIR)

coq-extract: clean-extract coq

clean: clean-extract
	$(MAKE) -C $(COQ_DIR) clean

clean-extract:
	rm -f $(COQ_DIR)/Extract.vo $(OCAML_DIR)/lib/extracted/*.ml*
