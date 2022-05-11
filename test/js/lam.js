var f = x => y => ((x + (y * 2)) + 5);
var g = f(3);
var h = g(4);
var _ = console.log(h);
console.log(f(3)(4))