include test-files.mk

.PHONY: test-js $(js_files) $(js_web_files)

test-js: $(js_files) $(js_web_files)

$(js_files):
	@MCORE_STDLIB=`pwd`/stdlib ./make run-js-test $@

$(js_web_files):
	@MCORE_STDLIB=`pwd`/stdlib ./make run-js-web-test $@
