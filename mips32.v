//  32-bit MIPS datapath in Verilog
//  Roneil Harris
//  Jim Kravchenko
//  SUNY New Paltz
//  Based on code from fpga4student.com
`timescale 1ns / 1ps

module mips_32( input clk,reset,
                          output[31:0] pc_out, alu_result,
                          reg_read_data_1, read_data2 // a, b
  );

  wire [2:0] ALU_Control;
  wire [31:0] ALU_out;
  wire zero_flag;
  wire signed[31:0] im_shift_2;
  wire signed[31:0]  PC_beq;
  wire signed[31:0] PC_4beq;
  wire signed[31:0] PC_4beqj;

  wire beq_control;

  wire sign_or_zero;
  wire [31:0] mem_read_data;
  wire [31:0] no_sign_ext;

//  wires going into instr_mem
   wire [31:0] instr;

//  wires coming from CONTROL
  //  2-bit
    wire[1:0] reg_dst;
    wire[1:0] mem_to_reg;
    wire[1:0] alu_op;
  //  1-bit
    wire jump;
    wire branch;
    wire mem_read;
    wire mem_write;
    wire alu_src;
    wire reg_write;



//  wires going into register memory
  wire     [4:0]     reg_write_dest;
  wire     [31:0] reg_write_data;
  wire     [4:0]     reg_read_addr_1;
  wire     [4:0]     reg_read_addr_2;
  wire     [31:0] reg_read_data_1;
  wire     [31:0] reg_read_data_2;

// select input to ALU
  wire [31:0] read_data2;

// PC program counter assigments
  reg[31:0] pc_current;
  wire[31:0] pc_next;
	wire[31:0] pc4;

// instruction memory
  instr_mem instrucion_memory(.pc(pc_current),.instruction(instr));

// PC + 4
	assign pc4 = pc_current + 32'd4;

// control unit
  control control_unit(.reset(reset),.opcode(instr[31:26]),.reg_dst(reg_dst)
                 ,.mem_to_reg(mem_to_reg),.alu_op(alu_op),.jump(jump),.branch(branch),.mem_read(mem_read),
                 .mem_write(mem_write),.alu_src(alu_src),.reg_write(reg_write),.sign_or_zero(sign_or_zero));

// multiplexer regdest
  // if reg_dst = 0, rd(instr[15:11]), else rt(instr[20:16])
  assign reg_write_dest = (reg_dst==2'b1) ?  instr[15:11] : instr[20:16];

// register file
   assign reg_read_addr_1 = instr[25:21];
   assign reg_read_addr_2 = instr[20:16];

   register_file reg_file(.clk(clk),.rst(reset),.reg_write_en(reg_write),
   .reg_write_dest(reg_write_dest),
   .reg_write_data(reg_write_data),
   .reg_read_addr_1(reg_read_addr_1),
   .reg_read_data_1(reg_read_data_1),
   .reg_read_addr_2(reg_read_addr_2),
   .reg_read_data_2(reg_read_data_2));

// ALU control unit
   ALUControl ALU_Control_unit(.ALUOp(alu_op),.Function(instr[5:0]),.ALU_Control(ALU_Control));

// ALU
  alu alu_unit(.a(reg_read_data_1),.b(read_data2),.alu_control(ALU_Control),.result(ALU_out),.zero(zero_flag));

// Multiplexer alu_src
  assign read_data2 = (alu_src==1'b1) ? sign_ext_im : reg_read_data_2;

// Sign Extend
  wire [31:0] sign_ext_im;
  assign sign_ext_im = {{16{instr[15]}},instr[15:0]};

// imm16 shift left 2
  assign im_shift_2 = {sign_ext_im[29:0],2'b0};
  assign no_sign_ext = ~(im_shift_2) + 1'b1;

 // BEQ
  // ADDER: BEQ + PC+4 (negative or positive)
    assign PC_beq = (im_shift_2[15] == 1'b1) ? (pc4 - no_sign_ext): (pc4 +im_shift_2);

  // BEQ Control Flags
 	  assign beq_control = branch & zero_flag; // AND GATE

	// BEQ select mux - depends on beq_control AND gate
 	  assign PC_4beq = (beq_control==1'b1) ? PC_beq : pc4;

  // PC_next gets assigned depending on branch
	 assign pc_next = PC_4beq;

// Data Memory
 	data_memory datamem(.clk(clk),.mem_access_addr(ALU_out),
 	.mem_write_data(reg_read_data_2),.mem_write_en(mem_write),.mem_read(mem_read),
 	.mem_read_data(mem_read_data));

// write back
 	assign reg_write_data = (mem_to_reg == 2'b0)? ALU_out: mem_read_data;

// Output
 	assign pc_out = pc_current;
 	assign alu_result = ALU_out;

// Program counter tick
  always @(posedge clk or posedge reset)
  begin
       if(reset)
            pc_current <= 31'd0;
       else
            pc_current <= pc_next;
  //$display("pc:  %0d, opcode: %0b",pc_current,instr[31:26]);
  end
endmodule


//`timescale 1ns / 1ps

module alu(
      input          [31:0]     a,          //src1
      input          [31:0]     b,          //src2
      input          [2:0]     alu_control,     //function sel
      output     reg     [31:0]     result,          //result
      output zero
   );
 always @(*)
 begin
      case(alu_control)
      3'b000: result = a + b; // add
      3'b001: result = a - b; // sub
      3'b010: result = a & b; // and
      3'b011: result = a | b; // or
      3'b100: begin if (a<b) result = 32'd1;
                     else result = 32'd0;
                     end
      default:result = a + b; // add
      endcase
 end
 assign zero = (result==32'd0) ? 1'b1: 1'b0;
 endmodule


//`timescale 1ns / 1ps

module ALUControl( ALU_Control, ALUOp, Function);
output reg[2:0] ALU_Control;
input [1:0] ALUOp;
input [5:0] Function;
  wire [7:0] ALUControlIn;
assign ALUControlIn = {ALUOp,Function};
always @(ALUControlIn)
casex (ALUControlIn)
 8'b11xxxx: ALU_Control=3'b000;//addi,lw,sw
 8'b01xxxx: ALU_Control=3'b001;//sub for beq
 8'b000000: ALU_Control=3'b000;//add
 8'b000001: ALU_Control=3'b001;//sub
 8'b000010: ALU_Control=3'b010;//and
 8'b000011: ALU_Control=3'b011;//or
 default: ALU_Control=3'b000;
 endcase
endmodule

// `timescale 1ns / 1ps

module control( input[5:0] opcode,
                          input reset,
                          output reg[1:0] reg_dst,mem_to_reg,alu_op,
                          output reg jump,branch,mem_read,mem_write,alu_src,reg_write,sign_or_zero
  );
always @(*)
begin
     if(reset == 1'b1) begin
               reg_dst = 2'b00;
               mem_to_reg = 2'b00;
               alu_op = 2'b00;
               jump = 1'b0;
               branch = 1'b0;
               mem_read = 1'b0;
               mem_write = 1'b0;
               alu_src = 1'b0;
               reg_write = 1'b0;
               sign_or_zero = 1'b1;
     end
     else begin
     case(opcode)
     6'b000: begin // add
               reg_dst = 2'b01;
               mem_to_reg = 2'b00;
               alu_op = 2'b00;
               jump = 1'b0;
               branch = 1'b0;
               mem_read = 1'b0;
               mem_write = 1'b0;
               alu_src = 1'b0;
               reg_write = 1'b1;
               sign_or_zero = 1'b1;
               end
     6'b100: begin // lw
               reg_dst = 2'b00;
               mem_to_reg = 2'b01;
               alu_op = 2'b11;
               jump = 1'b0;
               branch = 1'b0;
               mem_read = 1'b1;
               mem_write = 1'b0;
               alu_src = 1'b1;
               reg_write = 1'b1;
               sign_or_zero = 1'b1;
               end
     6'b101: begin // sw
               reg_dst = 2'b00;
               mem_to_reg = 2'b00;
               alu_op = 2'b11;
               jump = 1'b0;
               branch = 1'b0;
               mem_read = 1'b0;
               mem_write = 1'b1;
               alu_src = 1'b1;
               reg_write = 1'b0;
               sign_or_zero = 1'b1;
               end
     6'b110: begin // beq
               reg_dst = 2'b00;
               mem_to_reg = 2'b00;
               alu_op = 2'b01;
               jump = 1'b0;
               branch = 1'b1;
               mem_read = 1'b0;
               mem_write = 1'b0;
               alu_src = 1'b0;
               reg_write = 1'b0;
               sign_or_zero = 1'b1;
               end
     6'b111: begin // addi
               reg_dst = 2'b00;
               mem_to_reg = 2'b00;
               alu_op = 2'b11;
               jump = 1'b0;
               branch = 1'b0;
               mem_read = 1'b0;
               mem_write = 1'b0;
               alu_src = 1'b1;
               reg_write = 1'b1;
               sign_or_zero = 1'b1;
               end
     default: begin
               reg_dst = 2'b01;
               mem_to_reg = 2'b00;
               alu_op = 2'b00;
               jump = 1'b0;
               branch = 1'b0;
               mem_read = 1'b0;
               mem_write = 1'b0;
               alu_src = 1'b0;
               reg_write = 1'b1;
               sign_or_zero = 1'b1;
               end
     endcase
     end
end
endmodule


// `timescale 1ns / 1ps
module data_memory
(
     input                         clk,
     // address input, shared by read and write port
     input     [31:0]               mem_access_addr,
     // write port
     input     [31:0]               mem_write_data,
     input                         mem_write_en,
     input mem_read,
     // read port
     output     [31:0]               mem_read_data
);
     integer i;
     reg [31:0] ram [255:0];
     wire [7 : 0] ram_addr = mem_access_addr[8 : 1];
     initial begin
          for(i=0;i<256;i=i+1)
               ram[i] <= 32'd0;
     end

  	 always @(posedge clk) begin
          if (mem_write_en)
               ram[ram_addr] <= mem_write_data;
     end

     assign mem_read_data = (mem_read==1'b1) ? ram[ram_addr]: 32'd0;
endmodule





// `timescale 1ns / 1ps
module instr_mem
(
     input     [31:0]     pc,
     output wire     [31:0]          instruction
);
  wire [3 : 0] rom_addr = pc[5 : 2];
     reg [31:0] rom[15:0];
     reg [31:0]instrmem[0:14];
     reg [31:0] temp;

     always @(pc)
     begin
       temp=instrmem[rom_addr];
     end

     initial
     begin
       $readmemb("instr.txt", instrmem);
     end

//   prevent overflow
  assign instruction = temp;
  //  assign instruction = (pc[31:0] < 64 )? rom[rom_addr[3:0]]: 32'd0;
endmodule


//`timescale 1ns / 1ps
module register_file
(
     input                    clk,
     input                    rst,
     // write port
     input                    reg_write_en,
     input          [4:0]     reg_write_dest,
     input          [31:0]     reg_write_data,
     //read port 1 - rs 5-bit
     input          [4:0]     reg_read_addr_1,
     output          [31:0]     reg_read_data_1,
     //read port 2 -
     input          [4:0]     reg_read_addr_2,
     output          [31:0]     reg_read_data_2
);
     reg     [31:0]     reg_array [7:0];
     // write port
     always @ (posedge clk or posedge rst) begin
          if(rst) begin
               reg_array[0] <= 32'b0; // $zero
               reg_array[1] <= 32'b0;
               reg_array[2] <= 32'b0;
               reg_array[3] <= 32'b0;
               reg_array[4] <= 32'b0;
               reg_array[5] <= 32'b0;
               reg_array[6] <= 32'b0;
               reg_array[7] <= 32'b0;
          end
          else begin
               if(reg_write_en) begin
                    reg_array[reg_write_dest] <= reg_write_data;
                    //$display("%d written to reg %d",reg_write_data, reg_array[reg_write_dest]);

               end

          end
     end
     assign reg_read_data_1 = ( reg_read_addr_1 == 0)? 31'b0 : reg_array[reg_read_addr_1];
     assign reg_read_data_2 = ( reg_read_addr_2 == 0)? 31'b0 : reg_array[reg_read_addr_2];
endmodule
