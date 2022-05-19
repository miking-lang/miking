var a = 1;
if (({ c: { b: b } } = { b: 2, c: { b: a } })) {
  console.log(b);
  console.log(a);
} else console.log(false);
