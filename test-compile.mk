include test-files.mk

.PHONY: all selected $(src_files_all)

all: $(src_files_all)

selected: $(compile_files)

$(constrtype_files_exclude):
	@./make.sh compile-test $@ "build/mi compile --test --enable-constant-fold --disable-prune-utests"

$(filter-out $(constrtype_files_exclude), $(src_files_all)):
	@./make.sh compile-test $@ "build/mi compile --test --enable-constant-fold --disable-prune-utests --enable-constructor-types"
