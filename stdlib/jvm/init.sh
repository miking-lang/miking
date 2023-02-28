#!/bin/bash

if [ -d "jar/" ]
then 
    # compile Java program
    javac -cp jar/jackson-annotations-2.14.2.jar:jar/jackson-core-2.14.2.jar:jar/jackson-databind-2.14.2.jar:jar/asm-9.4.jar codegen/ClassfileMaker.java codegen/Parser.java -d out/
else 
    wget -P jar/ https://repo1.maven.org/maven2/com/fasterxml/jackson/core/jackson-core/2.14.2/jackson-core-2.14.2.jar 
    wget -P jar/ https://repo1.maven.org/maven2/com/fasterxml/jackson/core/jackson-databind/2.14.2/jackson-databind-2.14.2.jar  
    wget -P jar/ https://repo1.maven.org/maven2/com/fasterxml/jackson/core/jackson-annotations/2.14.2/jackson-annotations-2.14.2.jar
    wget -P jar/ https://repo1.maven.org/maven2/org/ow2/asm/asm/9.4/asm-9.4.jar 
    # compile Java program
    javac -cp jar/jackson-annotations-2.14.2.jar:jar/jackson-core-2.14.2.jar:jar/jackson-databind-2.14.2.jar:jar/asm-9.4.jar codegen/ClassfileMaker.java codegen/Parser.java -d out/
fi
