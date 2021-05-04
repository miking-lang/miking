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

all:
	@./make

test:
	@./make test

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
  test-compile\
  test-run\
  test-boot

test-compile:
	@$(MAKE) -s -f test-compile.mk all

test-run:
	@$(MAKE) -s -f test-run.mk all

test-boot:\
  test-boot-base\
  test-boot-par\
  test-boot-py\
  test-boot-ocaml

test-boot-base:
	@$(MAKE) -s -f test-boot.mk base

test-boot-par:
	@$(MAKE) -s -f test-boot.mk par

test-boot-sundials:
	@$(MAKE) -s -f test-boot.mk sundials

test-boot-py:
	@$(MAKE) -s -f test-boot.mk py

test-boot-ocaml:
	@$(MAKE) -s -f test-boot.mk ocaml

