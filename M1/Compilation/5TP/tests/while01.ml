var x;
x := 42;
while x != 0 begin
  var y;
  y := x / 2;
  print (x - 2 * y);
  x := y;
end
