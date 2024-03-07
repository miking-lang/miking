include test-files.mk

.PHONY: all selected $(src_files_all)

all: $(src_files_all)

selected: $(run_files)

$(constrtype_files_exclude):
	@./make.sh run-test $@ "build/mi run --test --disable-prune-warning"

$(filter-out $(constrtype_files_exclude), $(src_files_all)):
	@./make.sh run-test $@ "build/mi run --test --disable-prune-warning --enable-constructor-types"
