
tune_files += test/examples/tuning/tune-sleep.mc
tune_files += test/examples/tuning/tune-context.mc

.PHONY: all $(tune_files)

all: $(tune_files)

$(tune_files):
	@./make.sh compile-test $@ "build/mi tune --test --disable-optimizations --compile --disable-exit-early --enable-cleanup"
