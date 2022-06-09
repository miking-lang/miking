include test-files.mk

.PHONY: all $(accelerate_files)

all: $(accelerate_files)

$(accelerate_files):
	@./make compile-test $@ "build/mi compile --check-well-formed"
	@./make compile-test $@ "build/mi compile --accelerate"
