#!/bin/bash
###################################################
#  Modelyze II is licensed under the MIT license.  
#  Copyright (C) David Broman. See file LICENSE.txt
#
#  To make the build system platform independent,
#  all scripts are done in Ocaml instead of being
#  dependent on Make. If make is installed on
#  the system, we just run the batch make file.
###################################################

all:
	@./make

test:
	@./make test

clean:
	@./make clean
