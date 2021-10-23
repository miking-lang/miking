
compile_files += stdlib/sundials/sundials.mc

.PHONY: all $(compile_files)

all: $(compile_files)

$(compile_files):
	@./make compile-test $@ "build/mi compile --test --disable-optimizations"
