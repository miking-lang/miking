
BOOT_NAME=boot

base-files=
base-files+=$(wildcard test/mexpr/*.mc)
base-files+=$(wildcard test/mlang/*.mc)
base-files+=$(wildcard stdlib/mexpr/*.mc)
base-files+=$(wildcard stdlib/c/*.mc)
base-files+=$(wildcard stdlib/ad/*.mc)
base-files+=$(wildcard stdlib/parser/*.mc)

stdlib-root-files=$(wildcard stdlib/*.mc)

sundials-files=
sundials-files+=$(wildcard test/sundials/*.mc)
sundials-files+=$(wildcard stdlib/sundials/*.mc)

py-files=$(wildcard test/py/*.mc)

ocaml-files=$(wildcard stdlib/ocaml/*.mc)

# Rules

base: ${base-files} ${stdlib-root-files}
sundials: ${sundials-files}
py: ${py-files}
ocaml: ${ocaml-files}

# File rule
${base-files} ${par-files} ${sundials-files} ${py-files} ${ocaml-files}::
	-@build/${BOOT_NAME} eval --test $@

# These files require special handling to not conflict with the installed stdlib
${stdlib-root-files}::
	-@MCORE_STDLIB='@@@' build/${BOOT_NAME} eval --test $@
