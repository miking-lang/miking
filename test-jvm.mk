include test-files.mk

.PHONY: all $(jvm_files)

all: $(jvm_files)

$(jvm_files):
	@./make.sh compile-test $@ "build/mi compile --test --disable-optimizations --disable-prune-utests"
