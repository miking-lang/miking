BOOT_NAME=mi-boot
MI_LITE_NAME=mi-lite
MI_MID_NAME=mi-mid
MI_NAME=mi
MI_CHEAT_NAME=mi-cheat

prefix ?= $(HOME)/.local
bindir ?= $(prefix)/bin
libdir ?= $(prefix)/lib
mcoredir = $(libdir)/mcore
ifdef OPAM_SWITCH_PREFIX
opamlibdir = $(OPAM_SWITCH_PREFIX)/lib
endif
ocamllibdir ?= $(or $(opamlibdir), $(libdir)/ocaml/site-lib)

mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
current_dir := $(dir $(mkfile_path))
SET_STDLIB=MCORE_LIBS=stdlib=$(current_dir)/src/stdlib
ifdef OCAMLPATH
SET_OCAMLPATH=OCAMLPATH=$(current_dir)/build/lib:$(OCAMLPATH)
else
SET_OCAMLPATH=OCAMLPATH=$(current_dir)/build/lib
endif

j_flag := $(subst -j,-j ,$(filter -j%, $(MAKEFLAGS)))

.PHONY: default
default: bootstrap


# NOTE(vipa, 2023-03-29): This removes all ignored files in the build
# directory, which should coincide with generated files
.PHONY: clean
clean:
	misc/scripts/repo-ignored-files build | tr "\n" "\0" | xargs -r0 rm -f
	find build -depth -type d -empty -delete


# The OCaml library and executables (`boot`)

.PHONY: boot
boot:
	misc/scripts/with-tmp-dir dune build --root=src/boot/ --build-dir="{}" \
	"&&" dune install --root=src/boot/ --build-dir="{}" --prefix=$(current_dir)/build ">/dev/null" "2>&1"
	mv $(current_dir)"/build/bin/boot" build/$(BOOT_NAME)
	rm -f $(current_dir)"/build/lib/boot/dune-package"

.PHONY: install-boot
install-boot:
	misc/scripts/with-tmp-dir dune build --root=src/boot/ --build-dir="{}" \
	"&&" dune install --root=src/boot/ --build-dir="{}" --prefix=$(prefix) --libdir=$(ocamllibdir) ">/dev/null 2>&1"

.PHONY: uninstall-boot
uninstall-boot:
	misc/scripts/with-tmp-dir dune uninstall --root=src/boot --build-dir="{}" --prefix=$(prefix) --libdir=$(ocamllibdir) ">/dev/null 2>&1"


## Formatting, checking and autoformatting respectively

.PHONY: lint
lint:
	misc/scripts/with-tmp-dir dune build @fmt --root=src/boot/ --build-dir="{}"

.PHONY: fix
fix:
	misc/scripts/with-tmp-dir dune fmt --root=src/boot/ --build-dir="{}"


# Bootstrapping the `mi` executable

.PHONY: bootstrap
bootstrap: $(if $(wildcard build/$(BOOT_NAME)),,boot)
	$(SET_STDLIB) $(SET_OCAMLPATH) build/$(BOOT_NAME) eval src/main/mi-lite.mc -- 0 src/main/mi-lite.mc build/$(MI_LITE_NAME)
	$(SET_STDLIB) $(SET_OCAMLPATH) build/$(MI_LITE_NAME) 1 src/main/mi.mc build/$(MI_MID_NAME)
	$(SET_STDLIB) $(SET_OCAMLPATH) build/$(MI_MID_NAME) compile src/main/mi.mc --output build/$(MI_NAME)

build/$(MI_NAME): $(if $(wildcard build/$(MI_NAME)),,bootstrap)

.PHONY: cheat
cheat:
	$(SET_STDLIB) $(SET_OCAMLPATH) mi compile src/main/mi.mc --output build/$(MI_CHEAT_NAME)

build/$(MI_CHEAT_NAME): $(if $(wildcard build/$(MI_CHEAT_NAME)),,cheat)

# Umbrella install/uninstall targets, for installing and uninstalling everything

.PHONY: install
install: $(if $(wildcard build/$(MI_NAME)),,bootstrap) install-boot install-stdlib install-mi

.PHONY: uninstall
uninstall: uninstall-boot uninstall-stdlib uninstall-mi

# Installing and uninstalling `mi` and the standard library

.PHONY: install-mi
install-mi:
	mkdir -p $(bindir)
	cp -f build/$(MI_NAME) $(bindir)

.PHONY: install-stdlib
install-stdlib:
	mkdir -p $(mcoredir)
	rm -rf $(mcoredir)/stdlib || true
	cp -rf src/stdlib $(mcoredir)

.PHONY: uninstall-stdlib
uninstall-stdlib:
	rm -rf $(mcoredir)/stdlib

.PHONY: uninstall-mi
uninstall-mi:
	rm -f $(bindir)/$(MI_NAME)

# Basic testing (for more granular control, use `misc/test` directly)

misc/test: misc/test-spec.mc build/$(MI_NAME)
	$(SET_STDLIB) $(SET_OCAMLPATH) build/$(MI_NAME) compile misc/test-spec.mc --output misc/test

misc/scripts/parser-compare: misc/scripts/parser-compare.mc src/stdlib/parser/parser.mc build/$(MI_NAME)
	$(SET_STDLIB) $(SET_OCAMLPATH) build/$(MI_NAME) compile misc/scripts/parser-compare.mc --output misc/scripts/parser-compare

.PHONY: test test-all test-quick
test test-all test-quick: lint misc/test build/mi
test:
	+ exec misc/test $(j_flag) --boot --smart-dep

test-all:
	+ exec misc/test $(j_flag) --boot --most-dep

test-quick:
	+ exec misc/test $(j_flag) --boot --none-dep

test-info: misc/test
	@echo "Tasks run:" `find build/src/ -name '*.out' | wc -l`
	@misc/test --stats --boot --smart-dep
