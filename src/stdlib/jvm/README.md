# JVM Backend

If you want to use the JVM backend, start by running the init script:

`./init.sh`

Once the init script is done can compile an mexpr program like this:

```
mi compile --to-jvm program.mc >> out.json
./run.sh out.json
```

This will generate a classfile called `Hello.class` that can be run like this:

`java Hello`

Right now the compiler only supports print. Don't print any characters that need escaping, such as `\n`.