include test-files.mk

.PHONY: all $(mlang_pipeline_files)

all: $(mlang_pipeline_files)

$(mlang_pipeline_files):
	@./make.sh compile-test $@ "build/mi compile --test --mlang-pipeline"
	# @./make.sh compile-test $@ "build/mi compile --test --mlang-pipeline --disable-strict-sum-extension"
	
