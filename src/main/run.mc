

include "eval.mc"

-- In the future, we will implement 'run' in such a way that it creates two
-- parallel processes, where one process starts to evaluate the
-- program, and the other process compiles and then runs the exectable. The result
-- is then returned from the process that finishes first. Some things that
-- need to be considered: (i) should there be a delay before the compilation
-- starts, to not unnecessarily start the compilation process, and (ii)
-- how should side effects be handled?
let run = eval

