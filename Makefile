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
  test\
  install\
  install-boot\
  lint\
  fix\
  clean\
  old\
  test-compile\
  test-run\
  test-all\
  test-compile\
  test-run\
  test-boot\
  test-boot-base\
  test-sundials\
  test-par\
  test-boot-py\
  test-boot-ocaml

all: build/mi

boot:
	@./make boot

build/mi: boot
	@./make

test: test-boot-base

install: build/mi boot
	@./make install

install-boot: boot
	@./make install

lint:
	@./make lint

fix:
	@./make fix

clean:
	@./make clean

old:
	@./make old

test-all:\
  test-boot-compile\
  test-compile\
  test-run\
  test-par\
  test-boot

test-boot-compile: build/mi
	@$(MAKE) -s -f test-boot-compile.mk all

test-compile: build/mi
	@$(MAKE) -s -f test-compile.mk all

test-sundials: build/mi
	@$(MAKE) -s -f test-sundials.mk all

test-par: build/mi
	@$(MAKE) -s -f test-par.mk all

test-run: build/mi
	@$(MAKE) -s -f test-run.mk all

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
