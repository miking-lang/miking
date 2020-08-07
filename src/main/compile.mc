
-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "seq.mc"
let compile = lam files. lam options.
  let _ = [print "Files: ", dprint files, print "\n"] in
  print (join ["Option --debug-parse is ", if options.debugParse then "enabled" else "disabled", "."])
