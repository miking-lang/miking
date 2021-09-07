###################################################
#  Miking is licensed under the MIT license.
#  Copyright (C) David Broman. See file LICENSE.txt
#
#  To make the build system platform independent,
#  all scripts are done in OCaml instead of being
#  dependent on make. If make is installed on
#  the system, we just run the batch make file.
###################################################

.PHONY :\
  all\
  boot\
  install-boot\
  build\
  build-mi\
  install\
  lint\
  fix\
  clean\
  uninstall\
  test\
  test-all\
  test-boot-compile\
  test-compile\
  test-run\
  test-boot\
  test-boot-base\
  test-boot-py\
  test-boot-ocaml\
  test-sundials\
  test-par

all: build

boot:
	@./make boot

install-boot: boot
	@./make install-boot

build: install-boot	# Run the complete bootstrapping process to compile `mi`.
	@./make

build-mi:		# Build `mi` using the currently installed version.
	@./make build-mi

install: build
	@./make install

lint:
	@./make lint

fix:
	@./make fix

clean:
	@./make clean

uninstall:
	@./make uninstall

test: test-boot-base

test-all:\
  test-boot-compile\
  test-compile\
  test-run\
  test-par\
  test-boot

test-boot-compile: boot
	@$(MAKE) -s -f test-boot-compile.mk

test-compile: build
	@$(MAKE) -s -f test-compile.mk

test-run: build
	@$(MAKE) -s -f test-run.mk

test-boot:\
  test-boot-base\
  test-boot-py\
  test-boot-ocaml

test-boot-base: boot
	@$(MAKE) -s -f test-boot.mk base

test-boot-py: boot
	@$(MAKE) -s -f test-boot.mk py

test-boot-ocaml: boot
	@$(MAKE) -s -f test-boot.mk ocaml

test-sundials: build
	@$(MAKE) -s -f test-sundials.mk

test-par: build
	@$(MAKE) -s -f test-par.mk
