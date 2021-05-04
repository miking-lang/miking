###################################################
#  Miking is licensed under the MIT license.
#  Copyright (C) David Broman. See file LICENSE.txt
#
#  To make the build system platform independent,
#  all scripts are done in OCaml instead of being
#  dependent on make. If make is installed on
#  the system, we just run the batch make file.
###################################################

.PHONY : all test test-all install lint fix clean old files test-bootstrap test-compile test-bootstrap

all:
	@./make

test:
	@./make test

test-all:
	@./make test-all

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

test-compile:
	@$(MAKE) -s -f test-compile.mk all

test-run:
	@$(MAKE) -s -f test-run.mk all

test-bootstrap: test-compile test-run

