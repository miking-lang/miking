
BOOT_NAME = boot

base-files += $(wildcard test/mexpr/*.mc)
base-files += $(wildcard test/mlang/*.mc)
base-files += $(wildcard stdlib/mexpr/*.mc)
base-files += $(wildcard stdlib/c/*.mc)
base-files += $(wildcard stdlib/ad/*.mc)
base-files += $(wildcard stdlib/parser/*.mc)
base-files += $(wildcard stdlib/*.mc)

sundials-files += $(wildcard test/sundials/*.mc)
sundials-files += $(wildcard stdlib/sundials/*.mc)

py-files = $(wildcard test/py/*.mc)

ocaml-files = $(wildcard stdlib/ocaml/*.mc)

.PHONY: base sundials py ocaml\
  $(base-files) $(sundials-files) $(py-files) $(ocaml-files)

# Rules

base: $(base-files)
sundials: $(sundials-files)
py: $(py-files)
ocaml: $(ocaml-files)

# File rule
$(base-files) $(sundials-files) $(py-files) $(ocaml-files):
	-@MCORE_STDLIB=`pwd`/stdlib build/${BOOT_NAME} eval --test $@
