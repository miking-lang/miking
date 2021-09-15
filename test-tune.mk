
tune_files += test/examples/tuning/tune-sleep.mc
tune_files += test/examples/tuning/tune-context.mc

.PHONY: all $(tune_files)

all: $(tune_files)

$(tune_files):
	-@./make compile-test $@ "build/mi tune --test --disable-optimizations"
