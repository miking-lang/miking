include test-files.mk

BOOT_NAME = boot

.PHONY: all selected py $(src_files_all)

all: $(src_files_all)

selected: $(boot_files)

py: $(python_files)

# File rule
$(src_files_all):
	@MCORE_LIBS=stdlib=`pwd`/stdlib:test=`pwd`/test build/${BOOT_NAME} eval --test --disable-prune-warning $@
