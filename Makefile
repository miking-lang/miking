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
  test-boot-part\
  test-boot-sundials\
  test-boot-py\
  test-boot-ocaml

all: build/mi

boot:
	@./make boot
build/mi:
	@./make

test: test-boot-base

install:
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
  test-boot

test-boot-compile:
	@$(MAKE) -s -f test-boot-compile.mk all

test-compile: build/mi
	@$(MAKE) -s -f test-compile.mk all

test-run: build/mi
	@$(MAKE) -s -f test-run.mk all

test-boot:\
  test-boot-base\
  test-boot-par\
  test-boot-py\
  test-boot-ocaml

test-boot-base: boot
	@$(MAKE) -s -f test-boot.mk base

test-boot-par: build/mi
	@$(MAKE) -s -f test-boot.mk par

test-boot-sundials: build/mi
	@$(MAKE) -s -f test-boot.mk sundials

test-boot-py: build/mi
	@$(MAKE) -s -f test-boot.mk py

test-boot-ocaml: build/mi
	@$(MAKE) -s -f test-boot.mk ocaml
