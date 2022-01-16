include test-files.mk

.PHONY: all $(accelerate_files)

all: $(accelerate_files)

# Run the accelerated files with and without enabling the accelerated mode
$(accelerate_files):
	@./make compile-test $@ "build/mi compile --accelerate-futhark --cpu-only"
	@./make compile-test $@ "build/mi compile"
