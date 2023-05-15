BOOT_NAME=mi-boot
MI_LITE_NAME=mi-lite
MI_MID_NAME=mi-mid
MI_NAME=mi
MI_CHEAT_NAME=mi-cheat

BIN_PATH=$(HOME)/.local/bin
LIB_PATH=$(HOME)/.local/lib/mcore

mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
current_dir := $(dir $(mkfile_path))
SET_STDLIB=MCORE_LIBS=stdlib=$(current_dir)/src/stdlib
SET_OCAMLPATH=OCAMLPATH=$(current_dir)/build/lib

.PHONY: default
default: bootstrap

# NOTE(vipa, 2023-03-29): This removes all ignored files, which
# should coincide with generated files
.PHONY: clean
clean:
	bash -c 'mapfile -t args < <(misc/repo-ignored-files); rm -rf "$${args[@]}"'
	find build -depth -type d -empty -delete

# The OCaml library and executables (`boot`)

.PHONY: boot
boot: build/$(BOOT_NAME)
build/$(BOOT_NAME): $(shell find src/boot/ -type f)
	misc/with-tmp-dir dune build --root=src/boot/ --build-dir="{}" "&&" dune install --build-dir="{}" --prefix="{}/install-prefix" --root=src/boot/ --libdir=`pwd`/build/lib ">/dev/null" "2>&1" "&&" mv "{}/install-prefix/bin/boot" $@

.PHONY: install-boot
install-boot:
	misc/with-tmp-dir dune build --root=src/boot/ --build-dir="{}" "&&" dune install --root=src/boot/ --build-dir="{}" ">/dev/null 2>&1"

## Formatting, checking and autoformatting respectively

.PHONY: lint
lint:
	misc/with-tmp-dir dune fmt --root=src/boot/ --build-dir="{}"

.PHONY: fix
fix:
	misc/with-tmp-dir dune fmt --root=src/boot/ --build-dir="{}" --auto-promote

# Bootstrapping the `mi` executable

.PHONY: bootstrap
bootstrap: build/$(MI_NAME)

build/$(MI_LITE_NAME): build/$(BOOT_NAME)
	$(SET_STDLIB) $(SET_OCAMLPATH) time build/$(BOOT_NAME) eval src/main/mi-lite.mc -- 0 src/main/mi-lite.mc build/$(MI_LITE_NAME)

build/$(MI_MID_NAME): build/$(MI_LITE_NAME)
	$(SET_STDLIB) $(SET_OCAMLPATH) time build/$(MI_LITE_NAME) 1 src/main/mi.mc build/$(MI_MID_NAME)

build/$(MI_NAME): build/$(MI_MID_NAME)
	$(SET_STDLIB) $(SET_OCAMLPATH) time build/$(MI_MID_NAME) compile src/main/mi.mc --output build/$(MI_NAME)

.PHONY: cheat
cheat: build/$(MI_CHEAT_NAME)
build/$(MI_CHEAT_NAME): build/$(BOOT_NAME)
	$(SET_STDLIB) $(SET_OCAMLPATH) time mi compile src/main/mi.mc --output build/$(MI_CHEAT_NAME)

# Installing and uninstalling `mi` and the standard library

.PHONY: install
install: build/$(MI_NAME) install-boot
	rm -rf $(LIB_PATH)/stdlib || true
	mkdir -p $(BIN_PATH) $(LIB_PATH)
	cp -rf src/stdlib $(LIB_PATH)
	cp -f build/$(MI_NAME) $(BIN_PATH)

.PHONY: uninstall
uninstall:
	misc/with-tmp-dir dune uninstall --build-dir="{}" --root=src/boot
	rm -f $(BIN_PATH)/$(MI_NAME)
	rm -rf $(LIB_PATH)/stdlib

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
