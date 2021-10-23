
BOOT_NAME = boot

base-files += $(wildcard test/mexpr/*.mc)
base-files += $(wildcard test/mlang/*.mc)
base-files += $(wildcard stdlib/mexpr/*.mc)
base-files += $(wildcard stdlib/c/*.mc)
base-files += $(wildcard stdlib/ad/*.mc)
base-files += $(wildcard stdlib/parser/*.mc)
base-files += $(wildcard stdlib/*.mc)

py-files = $(wildcard test/py/*.mc)

ocaml-files = $(wildcard stdlib/ocaml/*.mc)

.PHONY: base py ocaml\
  $(base-files) $(py-files) $(ocaml-files)

# Rules

base: $(base-files)
py: $(py-files)
ocaml: $(ocaml-files)

# File rule
$(base-files) $(py-files) $(ocaml-files):
	@MCORE_STDLIB=`pwd`/stdlib build/${BOOT_NAME} eval --test $@
