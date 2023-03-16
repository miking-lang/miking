###################################################
#  Miking is licensed under the MIT license.
#  Copyright (C) David Broman. See file LICENSE.txt
#
#  To make the build system platform independent,
#  all scripts are done in OCaml instead of being
#  dependent on make. If make is installed on
#  the system, we just run the batch make.sh file.
###################################################

.PHONY :\
  all\
  boot\
  install-boot\
  build\
  build-mi\
  install\
  lite\
  lint\
  fix\
  clean\
  uninstall\
  test\
  test-all\
  test-boot-compile\
  test-boot-compile-all\
  test-compile\
  test-compile-all\
  test-all-prune-utests\
  test-boot-compile-prune-utests\
  test-boot-compile-prune-utests-all\
  test-compile-prune-utests\
  test-compile-prune-utests-all\
  test-run\
  test-run-all\
  test-run-boot\
  test-run-boot-all\
  test-boot\
  test-boot-all\
  test-boot-py\
  test-par\
  test-tune\
  test-sundials\
  test-ipopt\
  test-accelerate\
  test-jvm

all: build

boot:
	@./make.sh boot

install-boot: boot
	@./make.sh install-boot

lite: install-boot
	@./make.sh lite

test: test-boot

build: install-boot
# Run the complete bootstrapping process to compile `mi`.
	@./make.sh

build-mi:
# Build `mi` using the current version in `build`, skipping bootstrapping.
# The result is named `build/mi-tmp`.
	@./make.sh build-mi

install: build
	@./make.sh install

lint:
	@./make.sh lint

fix:
	@./make.sh fix

clean:
	@./make.sh clean

uninstall:
	@./make.sh uninstall

# Tests everything except some files with very special external dependencies
test-all:\
  test-boot-all\
  test-compile\
  test-run\
  test-js\
  test-tune\
  test-jvm
	@./make.sh lint

# The same as test-all but prunes utests whose external dependencies are not met
# on this system
test-all-prune-utests:\
  test-boot-all\
  test-compile-prune-utests\
  test-run\
	test-tune
	@./make.sh lint

test-boot-compile: boot
	@$(MAKE) -s -f test-boot-compile.mk selected

test-boot-compile-all: boot
	@$(MAKE) -s -f test-boot-compile.mk all

test-compile: build
	@$(MAKE) -s -f test-compile.mk selected

test-compile-all: build
	@$(MAKE) -s -f test-compile.mk all

test-boot-compile-prune-utests: boot
	@$(MAKE) -s -f test-boot-compile-prune-utests.mk selected

test-boot-compile-prune-utests-all: boot
	@$(MAKE) -s -f test-boot-compile-prune-utests.mk all

test-compile-prune-utests: build
	@$(MAKE) -s -f test-compile-prune-utests.mk selected

test-compile-prune-utests-all: build
	@$(MAKE) -s -f test-compile-prune-utests.mk all

test-run: build
	@$(MAKE) -s -f test-run.mk selected

test-run-all: build
	@$(MAKE) -s -f test-run.mk all

test-boot-run: install-boot
	@$(MAKE) -s -f test-boot-run.mk selected

test-boot-run-all: install-boot
	@$(MAKE) -s -f test-boot-run.mk all

test-boot: install-boot
	@$(MAKE) -s -f test-boot.mk selected

test-boot-py: boot
	@$(MAKE) -s -f test-boot.mk py

test-boot-all: install-boot
	@$(MAKE) -s -f test-boot.mk all

test-par: build
	@$(MAKE) -s -f test-par.mk

test-tune: build
	@$(MAKE) -s -f test-tune.mk

test-sundials: build
	@$(MAKE) -s -f test-sundials.mk

test-ipopt: build
	@$(MAKE) -s -f test-ipopt.mk

test-accelerate: build
	@$(MAKE) -s -f test-accelerate.mk

test-jvm: build
	@$(MAKE) -s -f test-jvm.mk

test-js: install-boot
	@$(MAKE) -s -f test-js.mk
