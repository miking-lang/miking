
compile_files =
compile_files += stdlib/sundials/sundials.mc

all: ${compile_files}

${compile_files}::
	-@./make compile-test $@ "build/mi compile --test --disable-optimizations"
