include test-files.mk

.PHONY: all selected $(src_files_all)

all: $(src_files_all)

selected: $(run_files)

$(src_files_all):
	@./make.sh run-test $@
