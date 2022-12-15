include test-files.mk

.PHONY: all selected $(src_files_all)

all: $(src_files_all)

selected: $(compile_files_prune)

$(src_files_all):
	@./make.sh compile-test $@ "build/mi compile --test --disable-optimizations"
