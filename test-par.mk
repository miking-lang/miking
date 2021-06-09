
compile_files =
compile_files += stdlib/multicore/atomic.mc
compile_files += stdlib/multicore/thread.mc

all: ${compile_files}

${compile_files}::
	-@./make compile-test $@ “build/mi compile --test --disable-optimizations”
