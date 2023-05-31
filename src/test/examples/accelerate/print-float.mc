mexpr

-- Explicit flushing of OCaml stdout to ensure it is printed first
print "OCaml float: ";
printFloat 3.14;
print "\n";
flushStdout ();

accelerate (
  print "CUDA float: ";
  printFloat 3.14;
  print "\n"
)
