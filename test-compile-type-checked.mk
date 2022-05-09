include test-files.mk

.PHONY: all selected $(src_files_all)

all: $(src_files_all)

selected: $(compile_files_typecheck)

$(src_files_all):
	@./make compile-test $@ "build/mi compile --test --disable-optimizations --disable-prune-utests --typecheck"
