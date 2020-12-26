module big_add(
    input wire [9 : 0] x,
    input wire [9 : 0] y,
    output wire nok
);
  assign nok = x * y != y * x;
endmodule
