include test-files.mk

.PHONY: all $(ipopt_files)

all: $(ipopt_files)

$(ipopt_files):
	@./make compile-test $@ "build/mi compile --test --disable-optimizations --disable-prune-utests"
