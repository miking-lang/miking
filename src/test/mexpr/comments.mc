-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt


-- This is a line comment

mexpr

/-
  A multiline
  comment.
-/

/-
  Nested multiline comments
  /-
    including line comments
    -- Another comment
  -/
-/

let x = /- multiline inside code -/ 1 in
utest x with 1 in

()
