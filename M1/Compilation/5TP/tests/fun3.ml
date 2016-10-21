fun f(x) begin return x + x ; end

fun g(x, y) begin return f(x) + f(f(y)); end

print g(1, 2);
