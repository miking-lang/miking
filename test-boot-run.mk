include test-files.mk

.PHONY: all selected $(src_files_all)

all: $(src_files_all)

selected: $(run_files)

$(src_files_all):
	@./make.sh run-test $@ "build/boot eval src/main/mi.mc -- run --test --disable-prune-warning"
