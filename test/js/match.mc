mexpr
	let a = 1 in
	match {c = {b = a}, b = 2} with {c = {b = b}} then
		print b
	else
		print false
