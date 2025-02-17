BOOT_NAME=mi-boot
MI_LITE_NAME=mi-lite
MI_MID_NAME=mi-mid
MI_NAME=mi
MI_CHEAT_NAME=mi-cheat

ifndef prefix
prefix=$(HOME)/.local
endif
ifndef bindir
bindir=$(prefix)/bin
endif
ifndef libdir
libdir=$(prefix)/lib
endif
ifdef OPAM_SWITCH_PREFIX
opamlibdir=$(OPAM_SWITCH_PREFIX)/lib
endif
ifndef ocamllibdir
ifdef opamlibdir
ocamllibdir=$(opamlibdir)
else
ocamllibdir=$(libdir)/ocaml/site-lib
endif
endif
mcoredir=$(libdir)/mcore

mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
current_dir := $(dir $(mkfile_path))
SET_STDLIB=MCORE_LIBS=stdlib=$(current_dir)/src/stdlib
ifdef OCAMLPATH
SET_OCAMLPATH=OCAMLPATH=$(current_dir)/build/lib:$(OCAMLPATH)
else
SET_OCAMLPATH=OCAMLPATH=$(current_dir)/build/lib
endif

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
	misc/scripts/with-tmp-dir dune fmt --root=src/boot/ --build-dir="{}"

.PHONY: fix
fix:
	misc/scripts/with-tmp-dir dune fmt --root=src/boot/ --build-dir="{}" --auto-promote


# Bootstrapping the `mi` executable

.PHONY: bootstrap
bootstrap: $(if $(wildcard build/$(BOOT_NAME)),,boot)
	$(SET_STDLIB) $(SET_OCAMLPATH) build/$(BOOT_NAME) eval src/main/mi-lite.mc -- 0 src/main/mi-lite.mc build/$(MI_LITE_NAME)
	$(SET_STDLIB) $(SET_OCAMLPATH) build/$(MI_LITE_NAME) 1 src/main/mi.mc build/$(MI_MID_NAME)
	$(SET_STDLIB) $(SET_OCAMLPATH) build/$(MI_MID_NAME) compile src/main/mi.mc --output build/$(MI_NAME)

.PHONY: cheat
cheat:
	$(SET_STDLIB) $(SET_OCAMLPATH) mi compile src/main/mi.mc --output build/$(MI_CHEAT_NAME)


# Installing and uninstalling `mi` and the standard library

.PHONY: install
install: $(if $(wildcard build/$(MI_NAME)),,bootstrap) install-boot
	mkdir -p $(bindir) $(mcoredir)
	cp -f build/$(MI_NAME) $(bindir)
	rm -rf $(mcoredir)/stdlib || true
	cp -rf src/stdlib $(mcoredir)

.PHONY: uninstall
uninstall:
	rm -f $(bindir)/$(MI_NAME)
	rm -rf $(mcoredir)/stdlib


# Basic testing (for more granular control, use `misc/test` directly,
# or `misc/watch` to autorun tests when files change)

.PHONY: test test-all test-quick
test test-all test-quick: $(if $(wildcard .tup/.),,build/$(MI_NAME))
test:
	exec misc/test --bootstrapped smart

test-all:
	exec misc/test --bootstrapped all

test-quick:
	exec misc/test --bootstrapped
