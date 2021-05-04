
BOOT_NAME=boot

base-files=
base-files+=$(wildcard test/mexpr/*.mc)
base-files+=$(wildcard test/mlang/*.mc)
base-files+=$(wildcard stdlib/mexpr/*.mc)
base-files+=$(wildcard stdlib/c/*.mc)
base-files+=$(wildcard stdlib/ad/*.mc)
base-files+=$(wildcard stdlib/parser/*.mc)
base-files+=$(wildcard stdlib/*.mc)

par-files=
par-files+=$(wildcard test/multicore/*.mc)
par-files+=$(wildcard stdlib/multicore/*.mc)

sundials-files=
sundials-files+=$(wildcard test/sundials/*.mc)
sundials-files+=$(wildcard stdlib/sundials/*.mc)

py-files=$(wildcard test/py/*.mc)

ocaml-files=$(wildcard stdlib/ocaml/*.mc)

# Rules
base: ${base-files}
par: ${par-files}
sundials: ${sundials-files}
py: ${py-files}
ocaml: ${ocaml-files}

# File rule
${base-files} ${par-files} ${sundials-files} ${py-files} ${ocaml-files}::
	-@build/${BOOT_NAME} eval --test $@
