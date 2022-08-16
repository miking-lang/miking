include test-files.mk

.PHONY: all $(accelerate_files)

all: $(accelerate_files)

$(accelerate_files):
	@./make compile-test $@ "build/mi compile --debug-accelerate"
	@./make compile-test $@ "build/mi compile --accelerate"
