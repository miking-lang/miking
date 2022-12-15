include test-files.mk

.PHONY: all $(sundials_files)

all: $(sundials_files)

$(sundials_files):
	@./make.sh compile-test $@ "build/mi compile --test --disable-optimizations --disable-prune-utests"
