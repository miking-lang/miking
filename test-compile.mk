include test-files.mk

.PHONY: all selected $(src_files_all)

all: $(src_files_all)

selected: $(compile_files)

$(src_files_all):
	@./make.sh compile-test $@ "build/mi compile --test --enable-constant-fold --disable-prune-utests"
