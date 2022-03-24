include test-files.mk

.PHONY: all $(cuda_files) $(futhark_files) $(accelerate_files)

all: $(cuda_files) $(futhark_files) $(accelerate_files)

$(accelerate_files):
	@./make compile-test $@ "build/mi compile"
	@./make compile-test $@ "build/mi compile --accelerate-cuda"
	@./make compile-test $@ "build/mi compile --accelerate-futhark"

$(cuda_files):
	@./make compile-test $@ "build/mi compile"
	@./make compile-test $@ "build/mi compile --accelerate-cuda"

$(futhark_files):
	@./make compile-test $@ "build/mi compile"
	@./make compile-test $@ "build/mi compile --accelerate-futhark"
