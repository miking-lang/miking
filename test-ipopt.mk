
compile_files =
compile_files += stdlib/ipopt/ipopt.mc

all: ${compile_files}

${compile_files}::
	-@./make compile-test $@ "build/mi compile --test --disable-optimizations"
