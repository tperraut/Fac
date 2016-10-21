fun f(x) begin
  var y;
  y := x + x; 
  begin var z; z := y * 3; print z; end
    var x;
  x := 5 + y;
  return x;
end

print f(1);
