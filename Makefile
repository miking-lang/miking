BOOT_NAME=boot
MI_LITE_NAME=mi-lite
MI_MID_NAME=mi-mid

BIN_PATH=$(HOME)/.local/bin
LIB_PATH=$(HOME)/.local/lib/mcore

.PHONY: default
default: bootstrap

# Misc and cleanup

build:
	mkdir -p build

# NOTE(vipa, 2023-03-29): This removes all ignored files, which
# should coincide with generated files
.PHONY: clean
clean:
	rm -rf $$(misc/repo-ignored-files)

# The OCaml library and executables (`boot`)

.PHONY: boot
boot: build/$(BOOT_NAME)
build/$(BOOT_NAME): build
	cd src/boot/ && dune build
	cd src/boot/ && dune install --prefix=../../build --bindir=`pwd`/../../build > /dev/null 2>&1

.PHONY: install-boot
install-boot:
	cd src/boot/ && dune install >/dev/null 2>&1

## Formatting, checking and autoformatting respectively

.PHONY: lint
lint:
	cd src/boot && dune build @fmt

.PHONY: fix
fix:
	cd src/boot && dune build @fmt --auto-promote

# Bootstrapping the `mi` executable

.PHONY: bootstrap
bootstrap: build/$(MI_NAME)

build/$(MI_LITE_NAME): build/$(BOOT_NAME)
	time build/$(BOOT_NAME) eval src/main/mi-lite.mc -- 0 src/main/mi-lite.mc build/$(MI_LITE_NAME)

build/$(MI_MID_NAME): build/$(MI_LITE_NAME)
	time build/$(MI_LITE_NAME) 1 src/main/mi.mc build/$(MI_MID_NAME)

build/$(MI_NAME): build/$(MI_MID_NAME)
	time build/$(MI_MID_NAME) compile src/main/mi.mc --output build/$(MI_NAME)

# Installing and uninstalling `mi` and the standard library

.PHONY: install
install: build/$(MI_NAME) install-boot
	rm -rf $(LIB_PATH)/stdlib || true
	mkdir -p $(BIN_PATH) $(LIB_PATH)
	cp -rf src/stdlib $(LIB_PATH)
	cp -f build/$(MI_NAME) $(BIN_PATH)

.PHONY: uninstall
uninstall:
	cd src/boot && dune uninstall
	rm -f $(BIN_PATH)/$(MI_NAME)
	rm -rf $(LIB_PATH)/stdlib

# Basic testing (for more granular control, use `misc/test` directly)

.PHONY: test test-all test-quick
test:
	misc/test smart

test-all:
	misc/test all

test-quick:
	misc/test

# TODO(vipa, 2023-03-28): write two things:
# - .mc program that outputs commands on how to build/run all tests, and does dependency checking
# - A shell script `misc/test` that evals the .mc program appropriately
