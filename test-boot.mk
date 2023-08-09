include test-files.mk

.PHONY: all selected py $(src_files_all)

all: $(src_files_all)

selected: $(boot_files)

py: $(python_files)

# File rule
$(src_files_all):
	@./make.sh run-test $@ "build/boot eval --test --disable-prune-warning"
