include test-files.mk

.PHONY: test-js $(js_files) $(js_web_files)

test-js: $(js_files) $(js_web_files)

$(js_files):
	@./make.sh run-js-test $@

$(js_web_files):
	@./make.sh run-js-web-test $@
