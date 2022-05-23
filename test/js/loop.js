let i = 10
loop:
while(true) {
  i = i - 1
  if (i < 0) {
    break loop
  }
  console.log("hello", i)
  continue loop;
}
