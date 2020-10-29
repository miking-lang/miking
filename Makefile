###################################################
#  Miking is licensed under the MIT license.
#  Copyright (C) David Broman. See file LICENSE.txt
#
#  To make the build system platform independent,
#  all scripts are done in OCaml instead of being
#  dependent on make. If make is installed on
#  the system, we just run the batch make file.
###################################################

.PHONY : all test clean

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
