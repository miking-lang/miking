let mexprBuiltInKeywords = [
  "if", "then", "else", "true", "false", "match", "with", "utest", "type",
  "con", "lang", "let", "recursive", "lam", "in", "end", "syn", "sem", "use",
  "mexpr", "include", "never", "using", "external", "switch", "case", "all"
]

let holeKeywords = ["hole", "Boolean", "IntRange", "independent"]

let accelerateKeywords = [
  "accelerate", "parallelMap", "flatten", "map2", "reduce", "seqLoop",
  "seqLoopAcc", "loop", "printFloat"]

let specializeKeywords = ["specialize"]

let mexprExtendedKeywords = concat specializeKeywords (
                              concat holeKeywords accelerateKeywords)
