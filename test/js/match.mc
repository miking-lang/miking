mexpr
	let a = 1 in
	match {c = a} with {c = b} then
		print b
	else
		print false
	-- let a = { b = 2 } in
	-- match a with { b = b } then
	-- 	print b
	-- else
	-- 	print false