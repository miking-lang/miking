mexpr
	let a = 1 in
	match {c = a, b = 2} with {c = c} then
		print c
	else
		print false

	-- let a = 1 in
	-- match {c = {b = a}} with {c = {b = b}} then
	-- 	print b
	-- else
	-- 	print false

	-- let a = { b = 2 } in
	-- match a with { b = b } then
	-- 	print b
	-- else
	-- 	print false
