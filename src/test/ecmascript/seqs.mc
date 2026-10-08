-- Sequences and strings.
--
-- No stdlib includes: `int2string` and friends use `recursive let`, not implemented yet.
-- Small integers are printed through a local digit helper, and larger
-- values through `float2string`, which is a builtin.
mexpr
let nl = "\n" in
let puts = lam s. print (concat s nl) in
let digit = lam n. [int2char (addi n (char2int '0'))] in
let putn = lam n. puts (digit n) in
let putf = lam x. puts (float2string x) in

-- Strings are ordinary sequences of characters.
puts "hello world";
puts (concat "ab" "cd");
puts (cons 'x' "yz");
puts (snoc "ab" 'c');
puts (reverse "abc");
puts (subsequence "hello" 1 3);
puts (tail "abc");
puts [head "abc"];
putn (length "hello");
putn (if null "" then 1 else 0);
putn (if null "a" then 1 else 0);
puts (map (lam c. int2char (addi (char2int c) 1)) "abc");
puts (set "abc" 1 'X');

-- Miking strings are codepoint sequences. This one is five characters, where
-- a JS string would report six, because the emoji is a surrogate pair there.
-- MCore has no \u escape, so the codepoint is built with int2char.
let emoji = [int2char 128512] in
let mixed = concat "ab" (concat emoji "cd") in
putn (length mixed);
putn (char2int (get mixed 2));

-- Sequences of other element types behave the same way.
let s = [1, 2, 3, 4, 5] in
putn (length s);
putn (get s 0);
putn (head s);
putn (length (tail s));
putn (length (concat s [6]));
putn (length (cons 0 s));
putn (length (snoc s 6));
putn (get (reverse s) 0);
putn (length (subsequence s 1 2));
putn (length (create 4 (lam i. i)));
putn (get (create 4 (lam i. muli i 2)) 3);
putn (length (splitAt s 2).0);
putn (length (splitAt s 2).1);
putn (if isList s then 1 else 0);
putn (if isRope s then 1 else 0);

-- Higher-order operations. The callbacks are curried, as MExpr requires.
putn (foldl (lam acc. lam x. addi acc x) 0 [1, 2, 3]);
putn (foldr (lam x. lam acc. subi x acc) 0 [1, 2, 3]);
puts (foldl (lam acc. lam c. cons c acc) "" "abc");
putn (get (mapi (lam i. lam x. addi i x) [10, 20, 30]) 2);
iter (lam c. print [c]) "iter"; print nl;
iteri (lam i. lam c. print (concat (digit i) [c])) "ab"; print nl;

-- Sequence patterns.
let classify = lam xs.
  match xs with [] then 0
  else match xs with [a] then a
  else match xs with [a, b] then addi a b
  else match xs with [a] ++ rest then addi a (length rest)
  else 99
in
putn (classify []);
putn (classify [7]);
putn (classify [3, 4]);
putn (classify [1, 1, 1, 1]);

-- An edge pattern with a postfix.
let ends = lam xs. match xs with [a] ++ _ ++ [b] then addi a b else 0 in
putn (ends [1, 9, 9, 2]);

-- Float and string conversions.
putf 1.0;
putf 0.1;
putf (divf 1.0 3.0);
putf 1e300;
putf (negf 2.5);
putf (string2float "2.5");
putn (if stringIsFloat "2.5" then 1 else 0);
putn (if stringIsFloat "abc" then 1 else 0)
