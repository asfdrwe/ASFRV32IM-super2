// Copyright (c) 2020, 2021 asfdrwe (asfdrwe@gmail.com)
// SPDX-License-Identifier: MIT
module PC(input wire clock, input wire reset_n,
          input wire [31:0] next_pc,
          output wire [31:0] pc_out, output wire [31:0] counter_out);
  reg [31:0] pc;
  reg [31:0] counter = 32'b0;
  assign pc_out = pc;
  assign counter_out = counter;

  // NEXT PC WRITE BACK and CYCLE COUNTER
  always @(posedge clock or negedge reset_n) begin
   if (!reset_n) begin
      pc <= 32'b0;
      counter <= 32'b0;
    end else begin
      pc <= #1 next_pc; 
      counter <= counter + 1;
    end
  end
endmodule

module INSTMEMORY(input wire clock,
                  input wire [31:0] pc, 
                  output wire [31:0] opcode_1, output wire [31:0] opcode_2, output wire [31:0] opcode_3);
  // INSTRUCTION MEMORY 64KB
  reg [31:0] mem[0:16'h3fff]; // MEMORY 64KB
  initial $readmemh("test.hex", mem); // MEMORY INITIALIZE 
  
  assign opcode_1 = mem[pc[31:2]];
  assign opcode_2 = mem[pc[31:2] + 1];
  assign opcode_3 = mem[pc[31:2] + 2];
endmodule

module PREDECODE(input wire [31:0] tmpopcode1, input wire [31:0] tmpopcode2, input wire [31:0] tmpopcode3, 
                 output wire [31:0] opcode_1, output wire [31:0] opcode_2, output wire [31:0] opcode_3, 
                 output wire [17:0] opcode_1_2,
                 output wire [1:0] superscalar, output wire isSPE1, output wire isSPE2);
  // INSTRUCTION OPCODE
  localparam [6:0] RFORMAT       = 7'b0110011;
  localparam [6:0] IFORMAT_ALU   = 7'b0010011;
  localparam [6:0] IFORMAT_LOAD  = 7'b0000011;
  localparam [6:0] SFORMAT       = 7'b0100011;
  localparam [6:0] SBFORMAT      = 7'b1100011;
  localparam [6:0] UFORMAT_LUI   = 7'b0110111;
  localparam [6:0] UFORMAT_AUIPC = 7'b0010111;
  localparam [6:0] UJFORMAT      = 7'b1101111;
  localparam [6:0] IFORMAT_JALR  = 7'b1100111;
  localparam [6:0] ECALLEBREAK   = 7'b1110011;
  localparam [6:0] FENCE         = 7'b0001111;
  localparam [6:0] MACROPFUSION1 = 7'b0001011;
  
  // Macro-Operation Fusion based on
  // https://people.eecs.berkeley.edu/~krste/papers/EECS-2016-130.pdf
  //
  // Extended Opcode
  //
  // Load Effective Address 
  // 31      25 24 20 19  15 14  12 11      7 6     0   17  1514          3 2  0
  // | 0000000shamt | rs1  |funct3 |  rd     |0001011| +|000  |0000000rs2  |010|
  // slli rd, rs1, {1,2} (funct3=010 or 011)
  // add rd, rd, rs2
  //
  // Indexed Load
  // 31      25 24 20 19  15 14  12 11      7 6     0   17  1514          3 2  0
  // | 0x00000| rs2 | rs1  |funct3 |  rd     |0001011| +|memop|000000000000|011|
  // (add or any op) rd, rs1, rs2
  // lb or lbu or lh or lhu or lw rd, 0(rd)
  //
  // Fused Indexed Load
  // 31      25 24 20 19  15 14  12 11      7 6     0   17  1514          3 2  0
  // | 0000000shamt | rs1  |funct3 |  rd     |0001011| +|memop|0000000rs2  |111|
  // slli rd, rs1, {1,2} (funct3=010 or 011)
  // add  rd, rd, rs2
  // lb or lbu or lh or lhu or lw rd, 0(rd)
  //
  // Load Immediate Idiom1
  // 31      25 24 20 19  15 14  12 11      7 6     0   17  1514          3 2  0
  // | imm[31:12]                   |  rd    |0001011| +|000  |imm[11:0]   |100|
  // lui rd, imm[31:12]
  // addi rd, rd, imm[11:0]
  //
  // Load Immediate Idiom2
  // 31      25 24 20 19  15 14  12 11      7 6     0   17  1514          3 2  0
  // | imm[31:12]                   |  rd    |0001011| +|memop|imm[11:0]   |101|
  // lui rd, imm[31:12]
  // lb or lbu or lh or lhu or lw rd, imm[11:0](rd)
  //
  // Wide Multiply/Divide & Remainder
  // 31      25 24 20 19  15 14  12 11      7 6     0   17  1514          3 2  0
  // | funct7   | rs2 | rs1  |funct3|  rdl   |0001011| +|000  |0000000rsh  |001|
  // mulh[[s]u] rdh, rs1, rs2
  // mul        rdl, rs1, rs2
  //
  // Load-pair/Store-pair (load1)
  // 31      25 24 20 19  15 14  12 11      7 6     0   17  1514          3 2  0
  // | imm[11:0]      | rs1  |010  |  rd1    |0001011| +|000  |0000000rd2  |110|
  // lw    rd1, imm(rs1)
  // lw    rd2, imm+4(rs1)
  //
  // Load-pair/Store-pair (load2)
  // 31      25 24 20 19  15 14  12 11      7 6     0   17  1514          3 2  0
  // | imm[11:0]      | rs1  |010  |  rd1    |0001011| +|010  |0000000rd2  |110|
  // lw    rd1, imm(rs1)
  // lw    rd2, imm-4(rs1)
  //
  // Load-pair/Store-pair (save1)
  // 31      25 24 20 19  15 14  12 11      7 6     0   17  1514          3 2  0
  // |imm[11:5] | rs2 | rs1  |010  |imm[4:0] |0001011| +|001  |0000000rs3  |110|
  // sw    rs2, imm(rs1)
  // sw    rs3, imm+4(rs1)
  //
  // Load-pair/Store-pair (save2)
  // 31      25 24 20 19  15 14  12 11      7 6     0   17  1514          3 2  0
  // |imm[11:5] | rs2 | rs1  |010  |imm[4:0] |0001011| +|011  |0000000rs3  |110|
  // sw    rs2, imm(rs1)
  // sw    rs3, imm-4(rs1)
  //
  // Load-trio/Store-trio (loadt1)
  // 31      25 24 20 19  15 14  12 11      7 6     0   17  1514          3 2  0
  // | imm[11:0]      | rs1  |010  |  rd1    |0001011| +|000  |00rd3rd2    |000|
  // lw    rd1, imm(rs1)
  // lw    rd2, imm+4(rs1)
  // lw    rd3, imm+8(rs1)
  //
  // Load-trio/Store-trio (loadt2)
  // 31      25 24 20 19  15 14  12 11      7 6     0   17  1514          3 2  0
  // | imm[11:0]      | rs1  |010  |  rd1    |0001011| +|010  |00rd3rd2    |000|
  // lw    rd1, imm(rs1)
  // lw    rd2, imm-4(rs1)
  // lw    rd3, imm-8(rs1)
  //
  // Load-trio/Store-trio (savet1)
  // 31      25 24 20 19  15 14  12 11      7 6     0   17  1514          3 2  0
  // |imm[11:5] | rs2 | rs1  |010  |  rd1    |0001011| +|001  |00rs4rs3    |000|
  // sw    rs2, imm(rs1)
  // sw    rs3, imm+4(rs1)
  // sw    rs4, imm+8(rs1)
  //
  // Load-trio/Store-trio (savet2)
  // 31      25 24 20 19  15 14  12 11      7 6     0   17  1514          3 2  0
  // |imm[11:5] | rs2 | rs1  |010  |  rd1    |0001011| +|011  |00rs4rs3    |000|
  // sw    rs2, imm(rs1)
  // sw    rs3, imm-4(rs1)
  // sw    rs4, imm-8(rs1)
  //
  localparam [2:0] MOF_LEA  = 3'b010;
  localparam [2:0] MOF_IL   = 3'b011;
  localparam [2:0] MOF_FIL  = 3'b111;
  localparam [2:0] MOF_LII1 = 3'b100;
  localparam [2:0] MOF_LII2 = 3'b101;
  localparam [2:0] MOF_WMDR = 3'b001;
  localparam [2:0] MOF_LPSP = 3'b110;
  localparam [2:0] MOF_LTST = 3'b000;

  wire [6:0] tmpop1, tmpop2, tmpop3;
  wire [4:0] regd_1, regd_2, regd_3;
  wire [4:0] reg1_1, reg2_1, reg1_2, reg2_2, reg1_3, reg2_3;
  wire [4:0] alucon_1, alucon_2, alucon_3;
  assign tmpop1 = tmpopcode1[6:0];
  assign tmpop2 = tmpopcode2[6:0];
  assign tmpop3 = tmpopcode3[6:0];
  assign alucon_1 = {tmpopcode1[30], tmpopcode1[25], tmpopcode1[14:12]};
  assign alucon_2 = {tmpopcode2[30], tmpopcode2[25], tmpopcode2[14:12]};
  assign alucon_3 = {tmpopcode3[30], tmpopcode3[25], tmpopcode3[14:12]};
  assign regd_1 = tmpopcode1[11:7];
  assign regd_2 = tmpopcode2[11:7];
  assign regd_3 = tmpopcode3[11:7];
  assign reg1_1 = tmpopcode1[19:15];
  assign reg2_1 = tmpopcode1[24:20];
  assign reg1_2 = tmpopcode2[19:15];
  assign reg2_2 = tmpopcode2[24:20];
  assign reg1_3 = tmpopcode3[19:15];
  assign reg2_3 = tmpopcode3[24:20];

  wire isBranch1, isBranch2; 
  wire isMemOp2, isMemOp3; // MEMORY OPERATION ONLY on exec1
  wire isMULDIV2, isMULDIV3; // MULDIV ONLY on exec1 
  wire isRegD_1, isRegD_2, isRegD_3;
  wire isReg1_1, isReg2_1, isReg1_2, isReg2_2, isReg1_3, isReg2_3;
  assign isBranch1 = (tmpop1 == UJFORMAT) || (tmpop1 == IFORMAT_JALR) || (tmpop1 == ECALLEBREAK); 
  assign isSPE1 = (tmpop1 == SBFORMAT);
  assign isBranch2 = (tmpop2 == UJFORMAT) || (tmpop2 == IFORMAT_JALR) || (tmpop2 == ECALLEBREAK); 
  assign isSPE2 = (tmpop2 == SBFORMAT);
  assign isMemOp2 = (tmpop2 == SFORMAT) || (tmpop2 == IFORMAT_LOAD);
  assign isMemOp3 = (tmpop3 == SFORMAT) || (tmpop3 == IFORMAT_LOAD);
  assign isMULDIV2 = (tmpop2 == RFORMAT) && (tmpopcode2[25] == 1'b1);
  assign isMULDIV3 = (tmpop3 == RFORMAT) && (tmpopcode3[25] == 1'b1);
  assign isRegD_1 = (regd_1 != 5'b0) &&
                  ((tmpop1 == RFORMAT) || (tmpop1 == IFORMAT_ALU) || (tmpop1 == IFORMAT_LOAD) || (tmpop1 == UFORMAT_LUI) || 
                   (tmpop1 == UFORMAT_AUIPC) || (tmpop1 == UJFORMAT) || (tmpop1 == IFORMAT_JALR));
  assign isRegD_2 = (regd_2 != 5'b0) &&
                  ((tmpop2 == RFORMAT) || (tmpop2 == IFORMAT_ALU) || (tmpop2 == IFORMAT_LOAD) || (tmpop2 == UFORMAT_LUI) || 
                   (tmpop2 == UFORMAT_AUIPC) || (tmpop2 == UJFORMAT) || (tmpop2 == IFORMAT_JALR));
  assign isReg1_2 = (reg1_2 != 5'b0) &&
                  ((tmpop2 == RFORMAT) || (tmpop2 == IFORMAT_ALU) || (tmpop2 == IFORMAT_LOAD) || (tmpop2 == SFORMAT) || 
                   (tmpop2 == SBFORMAT) || (tmpop2 == IFORMAT_JALR));
  assign isReg2_2 = (reg2_2 != 5'b0) &&
                  ((tmpop2 == RFORMAT) || (tmpop2 == SFORMAT) || (tmpop2 == SBFORMAT));
  assign isReg1_3 = (reg1_3 != 5'b0) &&
                  ((tmpop3 == RFORMAT) || (tmpop3 == IFORMAT_ALU) || (tmpop3 == IFORMAT_LOAD) || (tmpop3 == SFORMAT) || 
                   (tmpop3 == SBFORMAT) || (tmpop3 == IFORMAT_JALR));
  assign isReg2_3 = (reg2_3 != 5'b0) &&
                  ((tmpop3 == RFORMAT) || (tmpop3 == SFORMAT) || (tmpop3 == SBFORMAT));

  wire isFIL; // Fused Indexed Load
  assign isFIL = (tmpop1 == IFORMAT_ALU) && (alucon_1[2:0] == 3'b001) && ((tmpopcode1[24:20] == 5'b00001) || (tmpopcode1[24:20] == 5'b00010)) && // first  slli 1 or 2
                 (tmpop2 == RFORMAT) && (alucon_2 == 5'b00000) && // second add
                 (tmpop3 == IFORMAT_LOAD) && (tmpopcode3[31:20] == 12'b0) && // third lb or lh or ld with imm = 0
                 (regd_1 != 5'b0) && (regd_1 == reg1_2) && (regd_1 == regd_2) && (regd_2 == reg1_3) && (regd_2 == regd_3);
  wire isLEA; // Load Effective Address
  assign isLEA = !isFIL && ((tmpop1 == IFORMAT_ALU) && (alucon_1[2:0] == 3'b001) && ((tmpopcode1[24:20] == 5'b00001) || (tmpopcode1[24:20] == 5'b00010)) && // first  slli 1 or 2
                 (tmpop2 == RFORMAT) && (alucon_2 == 5'b00000) && // second add
                 (regd_1 != 5'b0) && (regd_1 == reg1_2) && (regd_1 == regd_2)); 
  wire isIL; // Indexed Load
  assign isIL = (tmpop1 == RFORMAT) && // first RFORMAT
                (tmpop2 == IFORMAT_LOAD) && (tmpopcode2[31:20] == 12'b0) && // second lb or lh or ld with imm = 0
                (regd_1 != 5'b0) && (regd_1 == reg1_2) && (regd_1 == regd_2);
  wire isLII1; // Load Immediate Idiom1
  assign isLII1 = (tmpop1 == UFORMAT_LUI) &&  // first LUI
                  (tmpop2 == IFORMAT_ALU) && (alucon_2[2:0] == 3'b000) &&  // second addi
                  (regd_1 != 5'b0) && (regd_1 == reg1_2) && (regd_1 == regd_2); 
  wire isLII2; // Load Immediate Idiom2
  assign isLII2 = (tmpop1 == UFORMAT_LUI) && // first LUI
                  (tmpop2 == IFORMAT_LOAD) && // second load
                  (regd_1 != 5'b0) && (regd_1 == reg1_2) && (regd_1 == regd_2);
  wire isWMDR; // Wide Multiply/Divide & Remainder
  wire [4:0] funct1, funct2, funct3;
  assign funct1 = {tmpopcode1[30], tmpopcode1[25], tmpopcode1[14:12]};
  assign funct2 = {tmpopcode2[30], tmpopcode2[25], tmpopcode2[14:12]};
  assign funct3 = {tmpopcode3[30], tmpopcode3[25], tmpopcode3[14:12]};
  wire isWM, isDR;
  assign isWM = ((funct1 == 5'b01001) || (funct1 == 5'b01010) || (funct1 == 5'b01011)) && (funct2 == 5'b01000);
  assign isDR = ((funct1 == 5'b01100) && (funct2 == 5'b01110)) ||
                ((funct1 == 5'b01101) && (funct2 == 5'b01111));
  assign isWMDR = (tmpop1 == RFORMAT) && (tmpopcode1[25] == 1'b1) &&
                  (tmpop2 == RFORMAT) && (tmpopcode2[25] == 1'b1) &&
                  (isWM || isDR) &&
                  (regd_1 != regd_2) && (reg1_1 == reg1_2) && (reg2_1 == reg2_2);
  wire isLPSP_LOAD, isLPSP_STORE, isLTST_LOAD, isLTST_STORE; // Load-pair/Store-pair/Load-trio/Store-trio
  wire [11:0] imm1, imm2, imm3;
  wire immplus4;
  assign immplus4 = ((imm2 - imm1) == 4);
  wire immminus4;
  assign immminus4 = ((imm1 - imm2) == 4);
  wire immplus8;
  assign immplus8 = ((imm3 - imm2) == 4) && ((imm2 - imm1) == 4);
  wire immminus8;
  assign immminus8 = ((imm2 - imm3) == 4) && ((imm1 - imm2) == 4);
  assign imm1 = (tmpop1 == IFORMAT_LOAD) ? tmpopcode1[31:20] : {tmpopcode1[31:25], tmpopcode1[11:7]};
  assign imm2 = (tmpop2 == IFORMAT_LOAD) ? tmpopcode2[31:20] : {tmpopcode2[31:25], tmpopcode2[11:7]};
  assign imm3 = (tmpop3 == IFORMAT_LOAD) ? tmpopcode3[31:20] : {tmpopcode3[31:25], tmpopcode3[11:7]};
  assign isLPSP_LOAD = (tmpop1 == IFORMAT_LOAD) && (tmpop2 == IFORMAT_LOAD) && (funct1 == 3'b010) && (funct2 == 3'b010) && (reg1_1 == reg1_2) && (immplus4 || immminus4);
  assign isLPSP_STORE = (tmpop1 == SFORMAT) && (tmpop2 == SFORMAT) && (funct1 == 3'b010) && (funct2 == 3'b010) && (reg1_1 == reg1_2) && (immplus4 || immminus4);
  assign isLTST_LOAD = (tmpop1 == IFORMAT_LOAD) && (tmpop2 == IFORMAT_LOAD) && (tmpop3 == IFORMAT_LOAD) && 
                       (funct1 == 3'b010) && (funct2 == 3'b010) && (funct3 == 3'b010) && 
                       (reg1_1 == reg1_2) && (reg1_1 == reg1_3) && (immplus8 || immminus8);
  assign isLTST_STORE = (tmpop1 == SFORMAT) && (tmpop2 == SFORMAT) && (tmpop3 == SFORMAT) && 
                       (funct1 == 3'b010) && (funct2 == 3'b010) && (funct3 == 3'b010) && 
                       (reg1_1 == reg1_2) && (reg1_1 == reg1_3) && (immplus8 || immminus8);

  wire [1:0] mopfusion;
  assign mopfusion = (isFIL || isLTST_LOAD || isLTST_STORE) ? 2'b10 : (isLEA || isIL || isLII1 || isLII2 || isWMDR || isLPSP_LOAD || isLPSP_STORE) ? 2'b01 : 2'b00;
  wire [11:0] mop_imm;
  assign mop_imm = tmpopcode2[31:20];

  assign superscalar = (mopfusion == 2'b10 ||
                       (mopfusion == 2'b01 && 
                        !isMemOp3 && !isMULDIV3 && // not MemOP3 && MULDIV3
                        (!isRegD_1 || (!isReg1_3 || (regd_1 != reg1_3)) && (!isReg2_3 || (regd_1 != reg2_3))) && // not REGISTER DEPENDANCY 1-3
                        (!isRegD_2 || (!isReg1_3 || (regd_2 != reg1_3)) && (!isReg2_3 || (regd_2 != reg2_3)))) || // not REGISTER DEPENDANCY 2-3
                       (!isBranch1 && !isBranch2 && // not BRANCH on 1,2
                        !isMemOp2 && !isMemOp3 && // not MemOP on 2,3
                        !isMULDIV2 && !isMULDIV3 && // not MULDIV on 2,3
                        (!isRegD_1 || (!isReg1_2 || (regd_1 != reg1_2)) && (!isReg2_2 || (regd_1 != reg2_2))) && // not REGISTER DEPENDANCY 1-2
                        (!isRegD_1 || (!isReg1_3 || (regd_1 != reg1_3)) && (!isReg2_3 || (regd_1 != reg2_3))) && // not REGISTER DEPENDANCY 1-3
                        (!isRegD_2 || (!isReg1_3 || (regd_2 != reg1_3)) && (!isReg2_3 || (regd_2 != reg2_3))))) ? 2'b10 : // not REGISTER DEPENDANCY 2-3
                        (mopfusion == 2'b01 ||
                        (!isBranch1 && // not BRANCH1
                        !isMemOp2 && // not MemOP2
                        !isMULDIV2 && // not MULDIV on 2
                        (!isRegD_1 || (!isReg1_2 || (regd_1 != reg1_2)) && (!isReg2_2 || (regd_1 != reg2_2))))) ? 2'b01 : // not REGISTER DEPENDANCY 1-2
                        2'b00;

  assign opcode_1 = (isLEA || isIL || isFIL || isLII1 || isLII2 || isWMDR || isLPSP_LOAD || isLPSP_STORE || isLTST_LOAD) ? {tmpopcode1[31:7], MACROPFUSION1} : tmpopcode1; // replace opcode to MACROPFUSION
  assign opcode_2 = ((mopfusion == 2'b00) && ((superscalar == 2'b10) || (superscalar == 2'b01))) ? tmpopcode2 : 32'b0;
  assign opcode_3 = ((mopfusion != 2'b10) && (superscalar == 2'b10)) ? tmpopcode3 : 32'b0;
  assign opcode_1_2 = isLEA        ? {3'b000,            7'b0, reg2_2,MOF_LEA } : // Load Effective Address
                      isIL         ? {tmpopcode2[14:12],       12'b0, MOF_IL  } : // Indexed Load
                      isFIL        ? {tmpopcode3[14:12], 7'b0, reg2_2,MOF_FIL } : // Fused Indexed Load
                      isLII1       ? {3'b000,                mop_imm, MOF_LII1} : // Load Immediate Idiom1
                      isLII2       ? {tmpopcode2[14:12],     mop_imm, MOF_LII2} : // Load Immediate Idiom2
                      isWMDR       ? {3'b000,           7'b0, regd_2, MOF_WMDR} : // Wide Multiply/Divide & Remainder
                      isLTST_LOAD  ? {1'b0,immminus8,1'b0,2'b0,regd_3,regd_2,MOF_LTST} : // Load-trio/Store-trio  (load)
                      isLTST_STORE ? {1'b0,immminus8,1'b1,2'b0,reg2_3,reg2_2,MOF_LTST} : // Load-trio/Store-trio  (store)
                      isLPSP_LOAD  ? {1'b0,immminus4,1'b0,7'b0,regd_2,MOF_LPSP} : // Load-pair/Store-pair  (load)
                      isLPSP_STORE ? {1'b0,immminus4,1'b1,7'b0,reg2_2,MOF_LPSP} : // Load-pair/Store-pair  (store)
                      18'b0;
endmodule

module DECODE(input wire [31:0] opcode, input wire [17:0] opcode_1_2,
              output wire [4:0] r_addr1, output wire [4:0] r_addr2, output wire [4:0] w_addr, output wire [31:0] imm,
              output wire [31:0] imm_0,
              output wire [4:0] alucon, output wire [2:0] funct3, output wire [2:0] op1sel, output wire op2sel,
              output wire mem_rw, output wire rf_wen, output wire [1:0] wb_sel, output wire [1:0] pc_sel, 
              output wire [4:0] extra_addr_1, output wire [2:0] extra_sel_1,
              output wire [4:0] extra_addr_2, output wire [2:0] extra_sel_2);

  wire [6:0] op;
  assign op = opcode[6:0];

  localparam [6:0] RFORMAT       = 7'b0110011;
  localparam [6:0] IFORMAT_ALU   = 7'b0010011;
  localparam [6:0] IFORMAT_LOAD  = 7'b0000011;
  localparam [6:0] SFORMAT       = 7'b0100011;
  localparam [6:0] SBFORMAT      = 7'b1100011;
  localparam [6:0] UFORMAT_LUI   = 7'b0110111;
  localparam [6:0] UFORMAT_AUIPC = 7'b0010111;
  localparam [6:0] UJFORMAT      = 7'b1101111;
  localparam [6:0] IFORMAT_JALR  = 7'b1100111;
  localparam [6:0] ECALLEBREAK   = 7'b1110011;
  localparam [6:0] FENCE         = 7'b0001111;
  localparam [6:0] MACROPFUSION1 = 7'b0001011;

  localparam [2:0] MOF_LEA  = 3'b010;
  localparam [2:0] MOF_IL   = 3'b011;
  localparam [2:0] MOF_FIL  = 3'b111;
  localparam [2:0] MOF_LII1 = 3'b100;
  localparam [2:0] MOF_LII2 = 3'b101;
  localparam [2:0] MOF_WMDR = 3'b001;
  localparam [2:0] MOF_LPSP = 3'b110;
  localparam [2:0] MOF_LTST = 3'b000;

  wire [2:0] op2;
  assign op2 = opcode_1_2[2:0];
  wire [4:0] op2_reg2;
  assign op2_reg2 = opcode_1_2[7:3]; // for LEA or FIL
  wire [2:0] op2_funct3;
  assign op2_funct3 = opcode_1_2[17:15];
  wire [11:0] op2_imm;
  assign op2_imm = opcode_1_2[14:3]; // for LII1 or LII2

  wire macroLEA;
  assign macroLEA  = (op == MACROPFUSION1) && (op2 == MOF_LEA ); // Load Effective Address
  wire macroIL;
  assign macroIL   = (op == MACROPFUSION1) && (op2 == MOF_IL  ); // Indexed Load
  wire macroFIL;
  assign macroFIL  = (op == MACROPFUSION1) && (op2 == MOF_FIL ); // Fused Indexed Load
  wire macroLII1;
  assign macroLII1 = (op == MACROPFUSION1) && (op2 == MOF_LII1); // Load Immediate Idiom1
  wire macroLII2;
  assign macroLII2 = (op == MACROPFUSION1) && (op2 == MOF_LII2); // Load Immediate Idiom2
  wire macroWMDR;
  assign macroWMDR = (op == MACROPFUSION1) && (op2 == MOF_WMDR); // Wide Multiply/Divide & Remainder
  wire immminus4, immmunus8;
  assign immminus4 = op2_funct3[1];
  assign immminus8 = op2_funct3[1];
  wire macroLPSP_LOAD;
  assign macroLPSP_LOAD = (op == MACROPFUSION1) && (op2 == MOF_LPSP) && ((op2_funct3 == 3'b000) || (op2_funct3 == 3'b010)); // Load-pair/Store-pair (load)
  wire macroLPSP_STORE;
  assign macroLPSP_STORE = (op == MACROPFUSION1) && (op2 == MOF_LPSP) && ((op2_funct3 == 3'b001) || (op2_funct3 == 3'b011)); // Load-pair/Store-pair (store)
  wire macroLTST_LOAD;
  assign macroLTST_LOAD = (op == MACROPFUSION1) && (op2 == MOF_LTST) && ((op2_funct3 == 3'b000) || (op2_funct3 == 3'b010)); // Load-trio/Store-trio (load)
  wire macroLTST_STORE;
  assign macroLTST_STORE = (op == MACROPFUSION1) && (op2 == MOF_LTST) && ((op2_funct3 == 3'b001) || (op2_funct3 == 3'b011)); // Load-trio/Store-trio (store)

  assign r_addr1 = (op == UFORMAT_LUI) ? 5'b0 : opcode[19:15];
  assign r_addr2 = (macroLEA || macroFIL) ? op2_reg2 : opcode[24:20];
  assign w_addr =  opcode[11:7];
  
  assign imm[31:20] = ((op == UFORMAT_LUI) || (op == UFORMAT_AUIPC) || macroLII1 || macroLII2) ? opcode[31:20] : {12{opcode[31]}};
  assign imm[19:12] = ((op == UFORMAT_LUI) || (op == UFORMAT_AUIPC) || (op == UJFORMAT) || macroLII1 || macroLII2) ? opcode[19:12] :  {8{opcode[31]}};
  assign imm[11] = (op == SBFORMAT) ? opcode[7] :
                   ((op == UFORMAT_LUI) || (op == UFORMAT_AUIPC) || macroLII1 || macroLII2) ? 1'b0 :
                   (op == UJFORMAT) ? opcode[20] : 
                                      opcode[31];
  assign imm[10:5] = ((op == UFORMAT_LUI) || (op == UFORMAT_AUIPC) || macroLII1 || macroLII2) ? 6'b0 : opcode[30:25];
  assign imm[4:1] = ((op == IFORMAT_ALU) || (op == IFORMAT_LOAD) || (op == IFORMAT_JALR) || (op == UJFORMAT) || macroLPSP_LOAD || macroLTST_LOAD) ? opcode[24:21] :
		    ((op == SFORMAT) || (op == SBFORMAT) || macroLPSP_STORE || macroLTST_STORE) ? opcode[11:8] : 
		                                            4'b0;
  assign imm[0] = ((op == IFORMAT_ALU) || (op == IFORMAT_LOAD) || (op == IFORMAT_JALR) || macroLPSP_LOAD || macroLTST_LOAD) ? opcode[20] :
		  ((op == SFORMAT) || macroLPSP_STORE || macroLTST_STORE) ? opcode[7] : 
		                    1'b0;
  assign imm_0 = {{20{op2_imm[11]}}, op2_imm};
  assign alucon = ((op == RFORMAT) || macroIL) ? {opcode[30], opcode[25], opcode[14:12]} :
                  macroWMDR ? {1'b1, opcode[25], opcode[14:12]} :
                  ((op == IFORMAT_ALU) && (opcode[14:12] == 3'b101)) ? {opcode[30], opcode[25], opcode[14:12]} : // SRLI or SRAI
                  (op == IFORMAT_ALU) ? {2'b00, opcode[14:12]} : 5'b0;
  assign funct3 = (macroIL || macroFIL || macroLII2) ? op2_funct3 : opcode[14:12];
  assign op1sel = ((macroLEA || macroFIL) && (opcode[21:20] == 2'b10)) ? 3'b110 :
                  ((macroLEA || macroFIL) && (opcode[21:20] == 2'b01)) ? 3'b101 :
                  (macroLII1 || macroLII2) ? 3'b010 :
                  ((op == SBFORMAT) || (op == UFORMAT_AUIPC) || (op == UJFORMAT)) ? 3'b001 : 3'b000;
  assign op2sel = ((op == RFORMAT) || macroLEA || macroIL || macroFIL || macroWMDR) ? 1'b0 : 1'b1;
  assign mem_rw = ((op == SFORMAT) || macroLPSP_STORE || macroLTST_STORE) ? 1'b1 : 1'b0;
  assign wb_sel = ((op == IFORMAT_LOAD) || macroIL || macroFIL || macroLII2 || macroLPSP_LOAD || macroLTST_LOAD) ? 2'b01 :
                  ((op == UJFORMAT) || (op == IFORMAT_JALR)) ? 2'b10 : 
                                                               2'b00;
  wire isShift;
  assign isShift = ({opcode[31:25], opcode[14:12]} == 10'b00000_00_001) || ({opcode[31], opcode[29:25], opcode[14:12]} == 9'b0_000_00_101);
  wire isALUIOP;
  assign isALUIOP = (opcode[14:12] == 3'b000) || (opcode[14:12] == 3'b010) || (opcode[14:12] == 3'b011) || (opcode[14:12] == 3'b100) || (opcode[14:12] == 3'b110) || (opcode[14:12] == 3'b111);
  assign rf_wen = (((op == RFORMAT) && ({opcode[31], opcode[29:26]} == 5'b00000)) ||
                   ((op == IFORMAT_ALU) && (isShift || isALUIOP)) ||
                    (op == IFORMAT_LOAD) || (op == UFORMAT_LUI) || (op == UFORMAT_AUIPC) || (op == UJFORMAT) || (op == IFORMAT_JALR)) ? 1'b1 :
                    (macroLEA || macroIL || macroFIL || macroLII1 || macroLII2 || macroWMDR || macroLPSP_LOAD || macroLTST_LOAD) ? 1'b1 :
                                                                                                     1'b0;
  assign pc_sel = (op == SBFORMAT) ? 2'b01 :
                  ((op == UJFORMAT) || (op == IFORMAT_JALR) || (op == ECALLEBREAK)) ? 2'b10 : 
                                                                                      2'b00;
  assign extra_addr_1 = opcode_1_2[7:3]; // for WMDR or LPSP
  assign extra_sel_1 = macroLTST_STORE ? {immminus8, 2'b11} : macroLTST_LOAD ? {immminus8, 2'b10} : macroLPSP_STORE ? {immminus4, 2'b11} : macroLPSP_LOAD ? {immminus4, 2'b10} : macroWMDR ? 3'b001 : 3'b000;
  assign extra_addr_2 = opcode_1_2[12:8]; // for LTST
  assign extra_sel_2 = macroLTST_STORE ? {immminus8, 2'b11} : macroLTST_LOAD ? {immminus8, 2'b10} : 3'b000;
endmodule

module DECODE_NOMOF(input wire [31:0] opcode, 
              output wire [4:0] r_addr1, output wire [4:0] r_addr2, output wire [4:0] w_addr, output wire [31:0] imm, 
              output wire [4:0] alucon, output wire [2:0] funct3, output wire op1sel, output wire op2sel,
              output wire mem_rw, output wire rf_wen, output wire [1:0] wb_sel, output wire [1:0] pc_sel);
  wire [6:0] op;
  assign op = opcode[6:0];

  localparam [6:0] RFORMAT       = 7'b0110011;
  localparam [6:0] IFORMAT_ALU   = 7'b0010011;
  localparam [6:0] IFORMAT_LOAD  = 7'b0000011;
  localparam [6:0] SFORMAT       = 7'b0100011;
  localparam [6:0] SBFORMAT      = 7'b1100011;
  localparam [6:0] UFORMAT_LUI   = 7'b0110111;
  localparam [6:0] UFORMAT_AUIPC = 7'b0010111;
  localparam [6:0] UJFORMAT      = 7'b1101111;
  localparam [6:0] IFORMAT_JALR  = 7'b1100111;
  localparam [6:0] ECALLEBREAK   = 7'b1110011;
  localparam [6:0] FENCE         = 7'b0001111;

  assign r_addr1 = (op == UFORMAT_LUI) ? 5'b0 : opcode[19:15];
  assign r_addr2 = opcode[24:20];
  assign w_addr =  opcode[11:7];

  assign imm[31:20] = ((op == UFORMAT_LUI) || (op == UFORMAT_AUIPC)) ? opcode[31:20] : {12{opcode[31]}};
  assign imm[19:12] = ((op == UFORMAT_LUI) || (op == UFORMAT_AUIPC) || (op == UJFORMAT)) ? opcode[19:12] :  {8{opcode[31]}};
  assign imm[11] = (op == SBFORMAT) ? opcode[7] :
                   ((op == UFORMAT_LUI) || (op == UFORMAT_AUIPC)) ? 1'b0 :
                   (op == UJFORMAT) ? opcode[20] : 
                                      opcode[31];
  assign imm[10:5] = ((op == UFORMAT_LUI) || (op == UFORMAT_AUIPC)) ? 6'b0 : opcode[30:25];
  assign imm[4:1] = ((op == IFORMAT_ALU) || (op == IFORMAT_LOAD) || (op == IFORMAT_JALR) || (op == UJFORMAT)) ? opcode[24:21] :
		    ((op == SFORMAT) || (op == SBFORMAT)) ? opcode[11:8] : 
		                                            4'b0;
  assign imm[0] = ((op == IFORMAT_ALU) || (op == IFORMAT_LOAD) || (op == IFORMAT_JALR)) ? opcode[20] :
		  (op == SFORMAT) ? opcode[7] : 
		                    1'b0;
  assign alucon = (op == RFORMAT) ? {opcode[30], opcode[25], opcode[14:12]} :
                  ((op == IFORMAT_ALU) && (opcode[14:12] == 3'b101)) ? {opcode[30], opcode[25], opcode[14:12]} : // SRLI or SRAI
                  (op == IFORMAT_ALU) ? {2'b00, opcode[14:12]} : 5'b0;
  assign funct3 = opcode[14:12];
  assign op1sel = ((op == SBFORMAT) || (op == UFORMAT_AUIPC) || (op == UJFORMAT)) ? 1'b1 : 1'b0;
  assign op2sel = (op == RFORMAT) ? 1'b0 : 1'b1;
  assign mem_rw = (op == SFORMAT) ? 1'b1 : 1'b0;
  assign wb_sel = (op == IFORMAT_LOAD) ? 2'b01 :
                  ((op == UJFORMAT) || (op == IFORMAT_JALR)) ? 2'b10 : 
                                                               2'b00;
  wire isShift;
  assign isShift = ({opcode[31:25], opcode[14:12]} == 10'b00000_00_001) || ({opcode[31], opcode[29:25], opcode[14:12]} == 9'b0_000_00_101);
  wire isALUIOP;
  assign isALUIOP = (opcode[14:12] == 3'b000) || (opcode[14:12] == 3'b010) || (opcode[14:12] == 3'b011) || (opcode[14:12] == 3'b100) || (opcode[14:12] == 3'b110) || (opcode[14:12] == 3'b111);
  assign rf_wen = (((op == RFORMAT) && ({opcode[31], opcode[29:26]} == 5'b00000)) ||
                   ((op == IFORMAT_ALU) && (isShift || isALUIOP)) ||
                    (op == IFORMAT_LOAD) || (op == UFORMAT_LUI) || (op == UFORMAT_AUIPC) || (op == UJFORMAT) || (op == IFORMAT_JALR)) ? 1'b1 : 
                                                                                                                                        1'b0;
  assign pc_sel = (op == SBFORMAT) ? 2'b01 :
                  ((op == UJFORMAT) || (op == IFORMAT_JALR) || (op == ECALLEBREAK)) ? 2'b10 : 
                                                                                      2'b00;
endmodule

module REGISTER(input wire clock,
                input wire rf_wen_1, input wire [4:0] w_addr_1, input wire [4:0] r_addr1_1, input wire [4:0] r_addr2_1,
                input wire [31:0] w_data_1, 
                output wire [31:0] r_data1_1, output wire [31:0] r_data2_1,
                input wire rf_wen_2, input wire [4:0] w_addr_2, input wire [4:0] r_addr1_2, input wire [4:0] r_addr2_2,
                input wire [31:0] w_data_2, 
                output wire [31:0] r_data1_2, output wire [31:0] r_data2_2,
                input wire rf_wen_3, input wire [4:0] w_addr_3, input wire [4:0] r_addr1_3, input wire [4:0] r_addr2_3,
                input wire [31:0] w_data_3, 
                output wire [31:0] r_data1_3, output wire [31:0] r_data2_3);
  // REGISTER 32bit x 32
  reg [31:0] regs[0:31];

  // REGISTER READ 1
  assign r_data1_1 = (r_addr1_1 == 5'b00000) ? 32'b0 : regs[r_addr1_1]; 
  assign r_data2_1 = (r_addr2_1 == 5'b00000) ? 32'b0 : regs[r_addr2_1]; 

  // REGISTER READ 2
  assign r_data1_2 = (r_addr1_2 == 5'b00000) ? 32'b0 : regs[r_addr1_2]; 
  assign r_data2_2 = (r_addr2_2 == 5'b00000) ? 32'b0 : regs[r_addr2_2]; 

  // REGISTER READ 3
  assign r_data1_3 = (r_addr1_3 == 5'b00000) ? 32'b0 : regs[r_addr1_3]; 
  assign r_data2_3 = (r_addr2_3 == 5'b00000) ? 32'b0 : regs[r_addr2_3]; 

  always @(posedge clock) begin
    // intentionally blocking assignment
    if (rf_wen_1 && (w_addr_1 != 5'b00000))
      regs[w_addr_1] = w_data_1;
    if (rf_wen_2 && (w_addr_2 != 5'b00000))
      regs[w_addr_2] = w_data_2;
    if (rf_wen_3 && (w_addr_3 != 5'b00000))
      regs[w_addr_3] = w_data_3;
  end
endmodule

module ALU(input wire [4:0] alucon, input wire [2:0] op1sel, input wire op2sel, 
           input wire [31:0] r_data1, input wire [31:0] pc, input wire [31:0] r_data2, input wire [31:0] imm,
           input wire [31:0] imm_0,
           output wire [31:0] alu_data, output wire [31:0] alu_extra_data);
  // SELECTOR  
  wire [31:0] s_data1, s_data2;
  assign s_data1 = (op1sel == 3'b110) ? (r_data1 << 2) :
                   (op1sel == 3'b101) ? (r_data1 << 1) :
                   (op1sel == 3'b010) ? imm_0 : 
                   (op1sel == 3'b001) ? pc : 
                                        r_data1;
  assign s_data2 = (op2sel == 1'b1) ? imm : r_data2;

  reg [31:0] tmpalu1, tmpalu2;

  function [63:0] ALU_EXEC(input [4:0] control, input [31:0] data1, input [31:0] data2);
    case(control)
    5'b00000: // ADD ADDI (ADD)
      ALU_EXEC = data1 + data2;
    5'b10000: // SUB (SUB)
      ALU_EXEC = data1 - data2;
    5'b00001: // SLL SLLI (SHIFT LEFT (LOGICAL))
      ALU_EXEC = data1 << data2[4:0];
    5'b00010: // SLT SLTI (SET_ON_LESS_THAN (SIGNED))
      ALU_EXEC = ($signed(data1) < $signed(data2)) ? 32'b1 :32'b0;
    5'b00011: // SLTU SLTUI (SET_ON_LESS_THAN (UNSIGNED))
      ALU_EXEC = (data1 < data2) ? 32'b1 :32'b0;
    5'b00100: // XOR XORI (XOR)
      ALU_EXEC = data1 ^ data2;
    5'b00101: // SRL SRLI (SHIFT RIGHT (LOGICAL))
      ALU_EXEC = data1 >> data2[4:0];
    5'b10101: // SRA SRAI (SHIFT RIGHT (ARITHMETIC))
      ALU_EXEC = $signed(data1[31:0]) >>> data2[4:0];
    5'b00110: // OR ORI (OR)
      ALU_EXEC = data1 | data2;
    5'b00111: // AND ANDI (AND)
      ALU_EXEC = data1 & data2;
    5'b01000: // MUL (MULTIPLE)
      ALU_EXEC = data1 * data2;
    5'b01001: begin // MULH (MULTIPLE)
      ALU_EXEC = $signed(data1) * $signed(data2);
    end
    5'b01010: begin // MULHSU (MULTIPLE)
      ALU_EXEC = $signed(data1) * $signed({1'b0, data2});
    end
    5'b01011: begin // MULHU (MULTIPLE)
      ALU_EXEC = data1 * data2;
    end
    5'b01100: // DIV (DIVIDE)
      ALU_EXEC = (data2 == 32'b0) ? 32'hffff_ffff : 
                 ((data1 == 32'h8000_0000) && (data2 == 32'hffff_ffff)) ? 32'h8000_0000 : 
                                                                          $signed($signed(data1) / $signed(data2));
    5'b01101: // DIVU (DIVIDE)
      ALU_EXEC = (data2 == 32'b0) ? 32'hffff_ffff : (data1 / data2);
    5'b01110: // REM (DIVIDE REMINDER)
      ALU_EXEC = (data2 == 32'b0) ? data1 : 
                 ((data1 == 32'h8000_0000) && (data2 == 32'hffff_ffff)) ? 32'h0 : 
                                                                          $signed($signed(data1) % $signed(data2));
    5'b01111: // REMU (DIVIDE REMINDER)
      ALU_EXEC = (data2 == 32'b0) ? data1 : (data1 % data2);
    5'b11001: // MULH + MUL
      ALU_EXEC = $signed(data1) * $signed(data2);
    5'b11010: // MULHSU + MUL
      ALU_EXEC = $signed(data1) * $signed({1'b0, data2});
    5'b11011: // MULHU + MUL
      ALU_EXEC = data1 * data2;
    5'b11100: begin // DIV + REM
      tmpalu1 = (data2 == 32'b0) ? 32'hffff_ffff :
                ((data1 == 32'h8000_0000) && (data2 == 32'hffff_ffff)) ? 32'h8000_0000 :
                                                                         $signed($signed(data1) / $signed(data2));
      tmpalu2 = (data2 == 32'b0) ? data1 :
                ((data1 == 32'h8000_0000) && (data2 == 32'hffff_ffff)) ? 32'h0 :
                                                                         $signed($signed(data1) % $signed(data2));
      ALU_EXEC = {tmpalu2, tmpalu1};
    end
    5'b11101: begin // DIVU + REMU
      tmpalu1 = (data2 == 32'b0) ? 32'hffff_ffff : (data1 / data2);
      tmpalu2 = (data2 == 32'b0) ? data1 : (data1 % data2);
      ALU_EXEC = {tmpalu2, tmpalu1};
    end
    default: // ILLEGAL
      ALU_EXEC = 64'b0;
    endcase
  endfunction

  wire [63:0] tmp;
  assign tmp = ALU_EXEC(alucon, s_data1, s_data2);
  assign {alu_extra_data, alu_data} = ((alucon == 5'b11001) || (alucon == 5'b11010) || (alucon == 5'b11011) || 
                                       (alucon == 5'b11100) || (alucon == 5'b11101)) ? tmp :
                                       (alucon == 5'b01001) ? ($signed(tmp) >>> 32) : 
                                      ((alucon == 5'b01010) || (alucon == 5'b01011)) ? (tmp >> 32) :
                                                                                      {32'b0, tmp[31:0]};
endmodule

module ALU_NOMULDIV(input wire [3:0] alucon, input wire op1sel, input wire op2sel, 
           input wire [31:0] r_data1, input wire [31:0] pc, input wire [31:0] r_data2, input wire [31:0] imm,
           output wire [31:0] alu_data);
  // SELECTOR  
  wire [31:0] s_data1, s_data2;
  assign s_data1 = (op1sel == 1'b1) ? pc : r_data1;
  assign s_data2 = (op2sel == 1'b1) ? imm : r_data2;

  reg [63:0] tmpalu;

  function [31:0] ALU_EXEC(input [4:0] control, input [31:0] data1, input [31:0] data2);
    case(control)
    4'b0000: // ADD ADDI (ADD)
      ALU_EXEC = data1 + data2;
    4'b1000: // SUB (SUB)
      ALU_EXEC = data1 - data2;
    4'b0001: // SLL SLLI (SHIFT LEFT (LOGICAL))
      ALU_EXEC = data1 << data2[4:0];
    4'b0010: // SLT SLTI (SET_ON_LESS_THAN (SIGNED))
      ALU_EXEC = ($signed(data1) < $signed(data2)) ? 32'b1 :32'b0;
    4'b0011: // SLTU SLTUI (SET_ON_LESS_THAN (UNSIGNED))
      ALU_EXEC = (data1 < data2) ? 32'b1 :32'b0;
    4'b0100: // XOR XORI (XOR)
      ALU_EXEC = data1 ^ data2;
    4'b0101: // SRL SRLI (SHIFT RIGHT (LOGICAL))
      ALU_EXEC = data1 >> data2[4:0];
    4'b1101: // SRA SRAI (SHIFT RIGHT (ARITHMETIC))
      ALU_EXEC = $signed(data1[31:0]) >>> data2[4:0];
    4'b0110: // OR ORI (OR)
      ALU_EXEC = data1 | data2;
    4'b0111: // AND ANDI (AND)
      ALU_EXEC = data1 & data2;
    default: // ILLEGAL
      ALU_EXEC = 32'b0;
    endcase
  endfunction
  
  assign alu_data = ALU_EXEC(alucon, s_data1, s_data2);
endmodule

module BRANCH(input wire [2:0] funct3, input [1:0] pc_sel,
           input wire [31:0] r_data1, input wire [31:0] r_data2, 
           output wire pc_sel2);
  function BRANCH_EXEC( input [2:0] branch_op, input [31:0] data1, input [31:0] data2, input [1:0] pc_sel);
    case(pc_sel)
    2'b00: // PC + 4
      BRANCH_EXEC = 1'b0;
    2'b01: begin // BRANCH
      case(branch_op)
      3'b000: // BEQ
        BRANCH_EXEC = (data1 == data2) ? 1'b1 : 1'b0;
      3'b001: // BNE
        BRANCH_EXEC = (data1 != data2) ? 1'b1 : 1'b0;
      3'b100: // BLT
        BRANCH_EXEC = ($signed(data1) < $signed(data2)) ? 1'b1 : 1'b0;
      3'b101: // BGE
        BRANCH_EXEC = ($signed(data1) >= $signed(data2)) ? 1'b1 : 1'b0;
      3'b110: // BLTU
        BRANCH_EXEC = (data1 < data2) ? 1'b1 : 1'b0;
      3'b111: // BGEU
        BRANCH_EXEC = (data1 >= data2) ? 1'b1 : 1'b0;
      default: // ILLEGAL
        BRANCH_EXEC = 1'b0;
      endcase
    end 
    2'b10: // JAL JALR
      BRANCH_EXEC = 1'b1;
    default: // ILLEGAL
      BRANCH_EXEC = 1'b0;
    endcase
  endfunction

  assign pc_sel2 = BRANCH_EXEC(funct3, r_data1, r_data2, pc_sel); 
endmodule

module DATAMEMORY(input clock,
              input wire mem_rw, input wire [2:0] mem_val, input wire [31:0] mem_addr, input wire [31:0] store_data,
              input wire [31:0] counter, output wire [8:0] uart_out,
              output wire [31:0] read_data,
              input wire [2:0] extra_sel_1, input wire [31:0] store_data_extra1, output wire [31:0] mem_extra_data_1,
              input wire [2:0] extra_sel_2, input wire [31:0] store_data_extra2, output wire [31:0] mem_extra_data_2);

  localparam [31:0] UART_MMIO_ADDR = 32'h0000_fff0; // ADDRESS 0xfff0 for UART DATA
  localparam [31:0] UART_MMIO_FLAG = 32'h0000_fff1; // ADDRESS 0xfff1 for UART FLAG
  localparam [31:0] COUNTER_MMIO_ADDR = 32'h0000_fff4; // ADDRESS 0xfff4 for COUNTER_MMIO_ADDR
  
  // UART
  reg [8:0] uart = 9'b0; // uart[8] for output sign, uart[7:0] for data1
  assign uart_out = uart;

  // DATA MEMORY 64KB 
  reg [31:0] mem[0:16'h3fff]; // MEMORY 64KB
  initial $readmemh("test.hex", mem); // MEMORY INITIALIZE 
  
  // MEMORY READ
  assign read_data = (mem_rw == 1'b1) ? 32'b0 : // when MEMORY WRITE, the output from MEMORY is 32'b0
		     ((mem_val == 3'b010) && (mem_addr == COUNTER_MMIO_ADDR)) ? counter : // MEMORY MAPPED IO for CLOCK CYCLE COUNTER
		     ((mem_val[1:0] == 2'b00) && (mem_addr == UART_MMIO_FLAG)) ? 8'b1 : // MEMORY MAPPED IO for UART FLAG(always enabled(8'b1))
                     ((mem_val == 3'b000) && (mem_addr[1:0] == 2'b00)) ? {{24{mem[mem_addr[31:2]][7]}},  mem[mem_addr[31:2]][7:0]} :  // LB
                     ((mem_val == 3'b000) && (mem_addr[1:0] == 2'b01)) ? {{24{mem[mem_addr[31:2]][15]}}, mem[mem_addr[31:2]][15:8]} : // LB
                     ((mem_val == 3'b000) && (mem_addr[1:0] == 2'b10)) ? {{24{mem[mem_addr[31:2]][23]}}, mem[mem_addr[31:2]][23:16]} : // LB
                     ((mem_val == 3'b000) && (mem_addr[1:0] == 2'b11)) ? {{24{mem[mem_addr[31:2]][31]}}, mem[mem_addr[31:2]][31:24]} : // LB
                     ((mem_val == 3'b001) && (mem_addr[1:0] == 2'b00)) ? {{16{mem[mem_addr[31:2]][15]}}, mem[mem_addr[31:2]][15:0]}  : // LH
                     ((mem_val == 3'b001) && (mem_addr[1:0] == 2'b10)) ? {{16{mem[mem_addr[31:2]][31]}}, mem[mem_addr[31:2]][31:16]} : // LH
                     ((mem_val == 3'b010) && (mem_addr[1:0] == 2'b00)) ? mem[mem_addr[31:2]] : // LW
                     ((mem_val == 3'b100) && (mem_addr[1:0] == 2'b00)) ? {24'h000000, mem[mem_addr[31:2]][7:0]} :  // LBU
                     ((mem_val == 3'b100) && (mem_addr[1:0] == 2'b01)) ? {24'h000000, mem[mem_addr[31:2]][15:8]} : // LBU
                     ((mem_val == 3'b100) && (mem_addr[1:0] == 2'b10)) ? {24'h000000, mem[mem_addr[31:2]][23:16]} : // LBU
                     ((mem_val == 3'b100) && (mem_addr[1:0] == 2'b11)) ? {24'h000000, mem[mem_addr[31:2]][31:24]} : // LBU
                     ((mem_val == 3'b101) && (mem_addr[1:0] == 2'b00)) ? {16'h0000, mem[mem_addr[31:2]][15:0]}  : // LHU
                     ((mem_val == 3'b101) && (mem_addr[1:0] == 2'b10)) ? {16'h0000, mem[mem_addr[31:2]][31:16]} : // LHU
                                                                        32'b0;
  assign mem_extra_data_1 = (!mem_rw && (mem_val == 3'b010) && (mem_addr[1:0] == 2'b00) && (extra_sel_1 == 3'b010)) ? 
                            ((mem_addr + 4) == COUNTER_MMIO_ADDR) ? counter : 
                                                                    mem[mem_addr[31:2] + 1] :  
                            (!mem_rw && (mem_val == 3'b010) && (mem_addr[1:0] == 2'b00) && (extra_sel_1 == 3'b110)) ? 
                            ((mem_addr - 4) == COUNTER_MMIO_ADDR) ? counter : 
                                                                    mem[mem_addr[31:2] - 1] :  
                            32'b0;
  assign mem_extra_data_2 = (!mem_rw && (mem_val == 3'b010) && (mem_addr[1:0] == 2'b00) && (extra_sel_2 == 3'b010)) ? 
                            ((mem_addr + 8) == COUNTER_MMIO_ADDR) ? counter : 
                                                                    mem[mem_addr[31:2] + 2] :  
                            (!mem_rw && (mem_val == 3'b010) && (mem_addr[1:0] == 2'b00) && (extra_sel_2 == 3'b110)) ? 
                            ((mem_addr - 8) == COUNTER_MMIO_ADDR) ? counter : 
                                                                    mem[mem_addr[31:2] - 2] :  
                            32'b0;

  // MEMORY WRITE
  always @(posedge clock) begin
    if (mem_rw == 1'b1) begin
      case (mem_val)
        3'b000: begin // SB
          case (mem_addr[1:0]) 
            2'b00: 
              mem[mem_addr[31:2]][7:0] <= #1 store_data[7:0];
            2'b01: 
              mem[mem_addr[31:2]][15:8] <= #1 store_data[7:0];
            2'b10: 
              mem[mem_addr[31:2]][23:16] <= #1 store_data[7:0];
            2'b11: 
              mem[mem_addr[31:2]][31:24] <= #1 store_data[7:0];
          endcase
        end
        3'b001: begin // SH
          case (mem_addr[1:0]) 
            2'b00: 
              mem[mem_addr[31:2]][15:0] <= #1 store_data[15:0];
            2'b10: 
              mem[mem_addr[31:2]][31:16] <= #1 store_data[15:0];
            default: begin end // misaligned
          endcase
        end
        3'b010: // SW
          if (mem_addr[1:0] == 2'b00) begin
            mem[mem_addr[31:2]] <= #1 store_data;
            if (extra_sel_1 == 3'b011) 
              mem[mem_addr[31:2] + 1] <= #1 store_data_extra1;
            else if (extra_sel_1 == 3'b111) 
              mem[mem_addr[31:2] - 1] <= #1 store_data_extra1;
            if (extra_sel_2 == 3'b011) 
              mem[mem_addr[31:2] + 2] <= #1 store_data_extra2;
            else if (extra_sel_2 == 3'b111) 
              mem[mem_addr[31:2] - 2] <= #1 store_data_extra2;
          end else begin end // misaligned
        default: begin end // ILLEGAL
      endcase
    end
    // MEMORY MAPPED IO to UART
    if ((mem_rw == 1'b1) && (mem_addr == UART_MMIO_ADDR)) begin
      uart <= #1 {1'b1, store_data[7:0]};
    end else if ((mem_rw == 1'b1) && (extra_sel_1 == 3'b011) && ((mem_addr + 4) == UART_MMIO_ADDR)) begin
      uart <= #1 {1'b1, store_data_extra1[7:0]};
    end else if ((mem_rw == 1'b1) && (extra_sel_1 == 3'b111) && ((mem_addr - 4) == UART_MMIO_ADDR)) begin
      uart <= #1 {1'b1, store_data_extra1[7:0]};
    end else if ((mem_rw == 1'b1) && (extra_sel_2 == 3'b011) && ((mem_addr + 8) == UART_MMIO_ADDR)) begin
      uart <= #1 {1'b1, store_data_extra2[7:0]};
    end else if ((mem_rw == 1'b1) && (extra_sel_2 == 3'b111) && ((mem_addr - 8) == UART_MMIO_ADDR)) begin
      uart <= #1 {1'b1, store_data_extra2[7:0]};
    end else begin
      uart <= #1 9'b0;
    end
  end
endmodule

module RV32IM(input wire clock, input wire reset_n, 
              output wire [31:0] pc_out, output wire [95:0] op_out, output wire[17:0] op2_out, output wire [95:0] alu_out, output wire [8:0] uart_out);
  // PROGRAM COUNTER & CYCLE COUNTER
  wire [31:0] pc, next_pc;
  wire [31:0] counter;
  PC pc1(clock, reset_n, next_pc, pc, counter);
  assign pc_out = pc; // for DEBUG

  // UART OUTPUT
  wire [8:0] uart;
  assign uart_out = uart;

  // FETCH
  wire [31:0] opcode_1, opcode_2, opcode_3;
  wire [17:0] opcode_1_2;
  wire [31:0] tmpopcode1, tmpopcode2,tmpopcode3;
  INSTMEMORY imem(clock, pc, tmpopcode1, tmpopcode2, tmpopcode3);

  // PREDECODE
  wire [1:0] superscalar;
  wire isSPE1, isSPEF1, isSPE2, isSPEF2;
  PREDECODE pre(tmpopcode1, tmpopcode2, tmpopcode3, opcode_1, opcode_2, opcode_3, opcode_1_2, superscalar, isSPE1, isSPE2);
  assign op_out = {opcode_3, opcode_2, opcode_1}; // for DEBUG
  assign op2_out = opcode_1_2;
  
  // DECODE

  // DECODE 1
  wire [4:0] r_addr1_1, r_addr2_1, w_addr_1;
  wire [31:0] imm_1, imm_1_0;
  wire [4:0] alucon_1;
  wire [2:0] funct3_1;
  wire [2:0] op1sel_1;
  wire op2sel_1, mem_rw_1, rf_wen_1;
  wire [1:0] wb_sel_1, pc_sel_1;
  wire [4:0] extra_addr_1;
  wire [2:0] extra_sel_1;
  wire [4:0] extra_addr_2;
  wire [2:0] extra_sel_2;

  wire [31:0] pc_1;
  assign pc_1 = pc;
  
  DECODE dec1(opcode_1, opcode_1_2, r_addr1_1, r_addr2_1, w_addr_1, imm_1, imm_1_0, alucon_1, funct3_1, op1sel_1, op2sel_1, mem_rw_1, rf_wen_1, wb_sel_1, pc_sel_1, extra_addr_1, extra_sel_1, extra_addr_2, extra_sel_2);

  // if SPECULATIVE EXECUTION2 FAILED
  assign isSPEF1 = (isSPE1 == 1'b1) && (pc_sel2_1 == 1'b1);
  
  // DECODE 2
  wire [4:0] r_addr1_2, r_addr2_2, w_addr_2;
  wire [31:0] imm_2;
  wire [4:0] alucon_2;
  wire [2:0] funct3_2;
  wire op1sel_2, op2sel_2, mem_rw_2, rf_wen_2;
  wire [1:0] wb_sel_2, pc_sel_2;
  wire pc_sel2_2;
  
  wire [31:0] pc_2;
  assign pc_2 = pc + 4;
  
  DECODE_NOMOF dec2(opcode_2, r_addr1_2, r_addr2_2, w_addr_2, imm_2, alucon_2, funct3_2, op1sel_2, op2sel_2, mem_rw_2, rf_wen_2, wb_sel_2, pc_sel_2);
  
  // if SPECULATIVE EXECUTION2 FAILED
  assign isSPEF2 = (isSPE2 == 1'b1) && (pc_sel2_2 == 1'b1);
  
  // DECODE 3
  wire [4:0] r_addr1_3, r_addr2_3, w_addr_3;
  wire [31:0] imm_3;
  wire [4:0] alucon_3;
  wire [2:0] funct3_3;
  wire op1sel_3, op2sel_3, mem_rw_3, rf_wen_3;
  wire [1:0] wb_sel_3, pc_sel_3;
  wire pc_sel2_3;
  
  wire [31:0] pc_3;
  assign pc_3 = pc + 8;
  
  DECODE_NOMOF dec3(opcode_3, r_addr1_3, r_addr2_3, w_addr_3, imm_3, alucon_3, funct3_3, op1sel_3, op2sel_3, mem_rw_3, rf_wen_3, wb_sel_3, pc_sel_3);

  // EXECUTION
  
  // REGISTER
  wire [31:0] w_data_1, r_data1_1, r_data2_1;  
  wire [31:0] w_data_2, r_data1_2, r_data2_2;
  wire [31:0] w_data_3, r_data1_3, r_data2_3;
  wire rf_wen_2_SPE, rf_wen_2_extra, rf_wen_3_SPE, rf_wen_3_extra;
  wire [4:0] r_addr2_2_extra, w_addr_2_extra;
  wire [4:0] r_addr2_3_extra, w_addr_3_extra;
  
  assign rf_wen_2_SPE = rf_wen_2 && !isSPEF1;
  assign rf_wen_2_extra = ((extra_sel_1 == 3'b001) || (extra_sel_1 == 3'b010) || (extra_sel_1 == 3'b110)) ? 1'b1 : rf_wen_2_SPE; // if MOF_WMDR or MOF_LP, set to 1
  assign r_addr2_2_extra = ((extra_sel_1 == 3'b011) || (extra_sel_1 == 3'b111)) ? extra_addr_1 : r_addr2_2; // if MOF_SP, use extra_addr_1 for STORE_DATA2
  assign w_addr_2_extra = ((extra_sel_1 == 3'b001) || (extra_sel_1 == 3'b010) || (extra_sel_1 == 3'b110)) ? extra_addr_1 : w_addr_2; // if MOF_WMDR or MOF_LP, use extra_addr_1 for W_DATA_2

  assign rf_wen_3_SPE = rf_wen_3 && !isSPEF1 && !isSPEF2;
  assign rf_wen_3_extra = ((extra_sel_2 == 3'b010) || (extra_sel_2 == 3'b110)) ? 1'b1 : rf_wen_3_SPE; // if MOF_LT, set to 1
  assign r_addr2_3_extra = ((extra_sel_2 == 3'b011) || (extra_sel_2 == 3'b111)) ? extra_addr_2 : r_addr2_3; // if MOF_ST, use extra_addr_2 for STORE_DATA3
  assign w_addr_3_extra = ((extra_sel_2 == 3'b010) || (extra_sel_2 == 3'b110)) ? extra_addr_2 : w_addr_3; // if MOF_LT, use extra_addr_2 for W_DATA_3
    
  REGISTER regs(clock, rf_wen_1, w_addr_1, r_addr1_1, r_addr2_1, w_data_1, r_data1_1, r_data2_1, 
                       rf_wen_2_extra, w_addr_2_extra, r_addr1_2, r_addr2_2_extra, w_data_2, r_data1_2, r_data2_2, 
                       rf_wen_3_extra, w_addr_3_extra, r_addr1_3, r_addr2_3_extra, w_data_3, r_data1_3, r_data2_3);
  
  // ALU 1
  wire [31:0] alu_data_1, alu_extra_data_1;
  ALU alu1(alucon_1, op1sel_1, op2sel_1, r_data1_1, pc_1, r_data2_1, imm_1, imm_1_0, alu_data_1, alu_extra_data_1);
  
  // BRANCH 1

  BRANCH branch1(funct3_1, pc_sel_1, r_data1_1, r_data2_1, pc_sel2_1);
  
  // ALU 2
  wire [31:0] alu_data_2;
  ALU_NOMULDIV alu2({alucon_2[4],alucon_2[2:0]}, op1sel_2, op2sel_2, r_data1_2, pc_2, r_data2_2, imm_2, alu_data_2);
  
  // BRANCH 2
  BRANCH branch2(funct3_2, pc_sel_2, r_data1_2, r_data2_2, pc_sel2_2);

  // ALU 3
  wire [31:0] alu_data_3;
  ALU_NOMULDIV alu3({alucon_3[4],alucon_3[2:0]}, op1sel_3, op2sel_3, r_data1_3, pc_3, r_data2_3, imm_3, alu_data_3);
  
  // BRANCH 3
  BRANCH branch3(funct3_3, pc_sel_3, r_data1_3, r_data2_3, pc_sel2_3);
  
  assign alu_out = {alu_data_3, alu_data_2, alu_data_1}; // for DEBUG

  // MEMORY
  
  // MEMORY 
  wire [31:0] mem_data_1, mem_extra_data_1, mem_extra_data_2;
  DATAMEMORY mem1(clock, mem_rw_1, funct3_1, alu_data_1, r_data2_1, counter, uart, mem_data_1, extra_sel_1, r_data2_2, mem_extra_data_1, extra_sel_2, r_data2_3, mem_extra_data_2);

  // WRITE BACK

  // REGISTER WRITE BACK 1
  assign w_data_1 = (wb_sel_1 == 2'b00) ? alu_data_1 : 
                    (wb_sel_1 == 2'b01) ? mem_data_1 :
                    (wb_sel_1 == 2'b10) ? pc_1 + 4 : 
                                          32'b0; // ILLEGAL
  // REGISTER WRITE BACK 2
  assign w_data_2 = ((extra_sel_1 == 3'b010) || (extra_sel_1 == 3'b110)) ? mem_extra_data_1 :
                    (extra_sel_1 == 3'b001) ? alu_extra_data_1 : 
                    (wb_sel_2 == 2'b00) ? alu_data_2 : 
                    (wb_sel_2 == 2'b10) ? pc_2 + 4 : 
                                          32'b0; // ILLEGAL

  // REGISTER WRITE BACK 3
  assign w_data_3 = ((extra_sel_2 == 3'b010) || (extra_sel_2 == 3'b110)) ? mem_extra_data_2 :
                    (wb_sel_3 == 2'b00) ? alu_data_3 : 
                    (wb_sel_3 == 2'b10) ? pc_3 + 4 : 
                                          32'b0; // ILLEGAL
  // NEXT PC
  assign next_pc = (superscalar == 2'b10) ? isSPEF1 ? {alu_data_1[31:1], 1'b0} :
                                            isSPEF2 ? {alu_data_2[31:1], 1'b0} : 
                                            (pc_sel2_3 == 1'b1) ? {alu_data_3[31:1], 1'b0} : 
                                                                  pc + 12 :
                   (superscalar == 2'b01) ? isSPEF1 ? {alu_data_1[31:1], 1'b0} :
                                            (pc_sel2_2 == 1'b1) ? {alu_data_2[31:1], 1'b0} : 
                                                                  pc +  8 :
					    (pc_sel2_1 == 1'b1) ? {alu_data_1[31:1], 1'b0} : 
					                          pc +  4 ;
endmodule
