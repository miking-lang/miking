
-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--

include "seq.mc"

let compile = lam options.
  print (join
    ["Option --debug-parse is ", if options.debugParse then "enabled" else "disabled", "."])
