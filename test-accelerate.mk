include test-files.mk

.PHONY: all $(accelerate_files)

all: $(accelerate_files)

$(accelerate_files):
	@./make.sh compile-test $@ "build/mi compile --debug-accelerate"
	@./make.sh compile-test $@ "build/mi compile --accelerate"
