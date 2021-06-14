
compile_files =
compile_files += stdlib/multicore/atomic.mc
compile_files += stdlib/multicore/thread.mc
compile_files += stdlib/multicore/channel.mc
compile_files += stdlib/multicore/thread-pool.mc

all: ${compile_files}

${compile_files}::
	-@./make compile-test $@ "build/mi compile --test --disable-optimizations"
