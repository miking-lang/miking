-- title: Unit tests

-- Each dot in the output indicate a passing unit test.

mexpr

-- Checks that the addition of 1 and 2 is in fact 3.
utest addi 1 2 with 3 in

-- Checks that the addition of 1 and 2 is not 0.
utest addi 1 2 with 0 using neqi in

-- With a custom failure message. Try changing 0 to 3.
utest addi 1 2 with 0 using neqi else lam l. lam r. "1+2 should not be 0" in

()
