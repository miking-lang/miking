include test-files.mk

.PHONY: all $(src_files_all)

all: $(src_files_all)

$(src_files_all):
	@ ./make.sh compile-and-run-jvm-test $@ 
