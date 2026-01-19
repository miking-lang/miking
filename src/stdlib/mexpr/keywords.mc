let mexprBuiltInKeywords = [
  "if", "then", "else", "true", "false", "match", "with", "utest", "type",
  "con", "lang", "let", "recursive", "lam", "in", "end", "syn", "sem", "use",
  "mexpr", "include", "never", "using", "external", "switch", "case", "all"
]

let opaqueKeywords = ["tmOpaque"]

let holeKeywords = ["hole", "Boolean", "IntRange", "independent"]

let accelerateKeywords = [
  "accelerate", "parallelMap", "flatten", "map2", "reduce", "seqLoop",
  "seqLoopAcc", "loop", "printFloat"]

let specializeKeywords = ["specialize"]

let mexprExtendedKeywords = foldl concat [] [opaqueKeywords, specializeKeywords, holeKeywords, accelerateKeywords]
