module big_add(
    input wire [255 : 0] x,
    input wire [255 : 0] y,
    output wire nok
);

  function [255 : 0] add256;
    input [255 : 0] a256;
    input [255 : 0] b256;

    wire [31 : 0] a32, b32, t32, c32;

    integer i;

    begin
      c32 = 32'h00000000;

      for (i = 0; i < 16; i = i + 1) begin
        a32 = {16'h0000, a256[i * 16 + 15 : i * 16]};
        b32 = {16'h0000, b256[i * 16 + 15 : i * 16]};
        t32 = a32 + b32 + c32;
        add256[i * 16 + 15 : i * 16] = t32[15 : 0];
        c32 = {16'h0000, t32[31 : 16]};
      end
    end
  endfunction

  assign nok = add256(x, y) != (x + y);
endmodule
