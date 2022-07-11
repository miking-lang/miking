include test-files.mk

.PHONY: test-js $(js_files)

js: $(js_files)

# File rule
$(js_files):
	@MCORE_STDLIB=`pwd`/stdlib ./make run-js-test $@
