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
                  output wire [31:0] opcode_1);
  // INSTRUCTION MEMORY 64KB 
  reg [31:0] mem[0:16'h3fff]; // MEMORY 64KB
  initial $readmemh("test.hex", mem); // MEMORY INITIALIZE 
  
  assign opcode_1 = mem[pc[31:2]];
endmodule

module DECODE(input wire [31:0] opcode, 
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
                output wire [31:0] r_data1_1, output wire [31:0] r_data2_1);
  // REGISTER 32bit x 32
  reg [31:0] regs[0:31];

  // REGISTER READ 1             
  assign r_data1_1 = (r_addr1_1 == 5'b00000) ? 32'b0 : regs[r_addr1_1]; 
  assign r_data2_1 = (r_addr2_1 == 5'b00000) ? 32'b0 : regs[r_addr2_1]; 

  always @(posedge clock) begin
    if (rf_wen_1 && (w_addr_1 != 5'b00000))
      regs[w_addr_1] <= #1 w_data_1;
  end
endmodule

module ALU(input wire [4:0] alucon, input wire op1sel, input wire op2sel, 
           input wire [31:0] r_data1, input wire [31:0] pc, input wire [31:0] r_data2, input wire [31:0] imm,
           output wire [31:0] alu_data);
  // SELECTOR  
  wire [31:0] s_data1, s_data2;
  assign s_data1 = (op1sel == 1'b1) ? pc : r_data1;
  assign s_data2 = (op2sel == 1'b1) ? imm : r_data2;

  reg [63:0] tmpalu;

  function [31:0] ALU_EXEC(input [4:0] control, input [31:0] data1, input [31:0] data2);
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
      tmpalu = $signed(data1) * $signed(data2);
      ALU_EXEC = $signed(tmpalu) >>> 32;
    end
    5'b01010: begin // MULHSU (MULTIPLE)
      tmpalu = $signed(data1) * $signed({1'b0, data2});
      ALU_EXEC = tmpalu >> 32;
    end
    5'b01011: begin // MULHU (MULTIPLE)
      tmpalu = data1 * data2;
      ALU_EXEC = tmpalu >> 32;
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
              output wire [31:0] read_data);

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
          if (mem_addr[1:0] == 2'b00)
            mem[mem_addr[31:2]] <= #1 store_data;
          else begin end // misaligned
        default: begin end // ILLEGAL
      endcase
    end
    // MEMORY MAPPED IO to UART
    if ((mem_rw == 1'b1) && (mem_addr == UART_MMIO_ADDR)) begin
      uart <= #1 {1'b1, store_data[7:0]};
    end else begin
      uart <= #1 9'b0;
    end
  end
endmodule

module RV32IM(input wire clock, input wire reset_n, 
              output wire [31:0] pc_out, output wire [31:0] op_out, output wire [31:0] alu_out, output wire [8:0] uart_out);
  // PROGRAM COUNTER & CYCLE COUNTER
  wire [31:0] pc, next_pc;
  wire [31:0] counter;
  PC pc1(clock, reset_n, next_pc, pc, counter);
  assign pc_out = pc; // for DEBUG

  // UART OUTPUT
  wire [8:0] uart;
  assign uart_out = uart;
 
  // FETCH
  wire [31:0] opcode_1;
  INSTMEMORY imem(clock, pc, opcode_1);

  assign op_out = opcode_1; // for DEBUG

  // DECODE
  wire [4:0] r_addr1_1, r_addr2_1, w_addr_1;
  wire [31:0] imm_1;
  wire [4:0] alucon_1;
  wire [2:0] funct3_1;
  wire op1sel_1, op2sel_1, mem_rw_1, rf_wen_1;
  wire [1:0] wb_sel_1, pc_sel_1;

  wire [31:0] pc_1;
  assign pc_1 = pc;
  
  DECODE dec1(opcode_1, r_addr1_1, r_addr2_1, w_addr_1, imm_1, alucon_1, funct3_1, op1sel_1, op2sel_1, mem_rw_1, rf_wen_1, wb_sel_1, pc_sel_1);
  
  // EXECUTION
  
  // REGISTER
  wire [31:0] w_data_1, r_data1_1, r_data2_1;  
  REGISTER regs(clock, rf_wen_1, w_addr_1, r_addr1_1, r_addr2_1, w_data_1, r_data1_1, r_data2_1);
  
  // ALU
  wire [31:0] alu_data_1;
  ALU alu1(alucon_1, op1sel_1, op2sel_1, r_data1_1, pc_1, r_data2_1, imm_1, alu_data_1);

  assign alu_out = alu_data_1; // for DEBUG
  
  // BRANCH
  wire pc_sel2_1;
  BRANCH branch1(funct3_1, pc_sel_1, r_data1_1, r_data2_1, pc_sel2_1);
  
  // MEMORY 
  wire [31:0] mem_data_1;            
  DATAMEMORY mem1(clock, mem_rw_1, funct3_1, alu_data_1, r_data2_1, counter, uart, mem_data_1);

  // REGISTER WRITE BACK
  assign w_data_1 = (wb_sel_1 == 2'b00) ? alu_data_1 : 
                    (wb_sel_1 == 2'b01) ? mem_data_1 :
                    (wb_sel_1 == 2'b10) ? pc_1 + 4 : 
                                          32'b0; // ILLEGAL

  // NEXT PC
  assign next_pc = pc_sel2_1 ? {alu_data_1[31:1], 1'b0} : pc_1 + 4; 
endmodule
