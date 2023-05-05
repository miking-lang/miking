#!/bin/bash

# run java program
java -cp out/:jar/jackson-annotations-2.14.2.jar:jar/jackson-core-2.14.2.jar:jar/jackson-databind-2.14.2.jar:jar/asm-9.4.jar:jar/asm-util-9.4.jar:jar/asm-tree-9.4.jar:jar/asm-analysis-9.4.jar codegen/Parser $1
