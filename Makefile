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

sundials:
	@./make sundials

test:
	@./make test

test-sundials:
	@./make test-sundials

install:
	@./make install

install-sundials:
	@./make install-sundials

clean:
	@./make clean

old:
	@./make old
