`include "macros.sv"

//=================================================================
// ECE 745 ASIC Verification
// Final Project: LC3 Microprocessor Verification
// Class Name: decode
// Author: Mehrnaz Sadeghian
//=================================================================

`timescale 10ns / 1ps
class decode;

virtual decodeInterface deif;

typedef struct packed {
   logic [15:0]IR;
   logic [5:0]E_Control;
   logic [15:0]npc_out;
   logic Mem_Control;
   logic [1:0]W_Control;
} decode_gr;
int decode_err=0;
decode_gr golden_ref;

function new(virtual decodeInterface df);
	deif=df;
endfunction

task de_check(ref int decode_err_count) ;
	@(posedge deif.clock);
	golden_ref_chk();
	decode_err_count=decode_err_count+decode_err;
		if(decode_err>0)
			print_decode_err();
		decode_err=0;
	golden_ref_update();
	decode_err=0;
endtask

function void IR_print(logic [15:0] IR);
	case(IR[15:12])
  `ADD: begin
    if(IR[5])
	 $display($time, "ps [DECODE][OPCODE: IMMEDIATE ADD][DR: R%d][SR1: R%d][Imm5 value: %d]",IR[11:9],IR[8:6], IR[4:0]);
	else
	 $display($time, "ps [DECODE][OPCODE: ADD][DR: R%d][SR: R%d][SR2: R%d]",IR[11:9],IR[8:6], IR[2:0]);
  end
  `AND: begin
    if(IR[5])
	 $display($time, "ps [DECODE][OPCODE: IMMEDIATE AND][DR: R%d][SR1: R%d][Imm5 value: %d]",IR[11:9],IR[8:6], IR[4:0]);
	else
	 $display($time, "ps [DECODE][OPCODE: AND][DR: R%d][SR: R%d][SR2: R%d]",IR[11:9],IR[8:6], IR[2:0]);
  end
  `NOT: $display($time, "ps [DECODE][OPCODE: NOT][DR: R%d][SR1: R%d]",IR[11:9],IR[8:6]);
  `LD: $display($time, "ps [DECODE][OPCODE: LD][DR: R%d][PCOFFSET: %d]",IR[11:9],IR[8:0]);
  `LDR: $display($time, "ps [DECODE][OPCODE: LDR][DR: R%d][BASE_R: R%d][PCOFFSET: %d]",IR[11:9],IR[8:6],IR[5:0]);
  `LDI: $display($time, "ps [DECODE][OPCODE: LDI][DR: R%d][PCOFFSET: %d]",IR[11:9],IR[8:0]);
  `LEA: $display($time, "ps [DECODE][OPCODE: LEA][DR: R%d][PCOFFSET: %d]",IR[11:9],IR[8:0]);
  `ST: $display($time, "ps [DECODE][OPCODE: ST][SR: R%d][PCOFFSET: %d]",IR[11:9],IR[8:0]);
  `STR: $display($time, "ps [DECODE][OPCODE: STR][SR: R%d][BASE_R: R%d][PCOFFSET: %d]",IR[11:9], IR[8:6],IR[5:0]);
  `STI: $display($time, "ps [DECODE][OPCODE: STI][SR: R%d][PCOFFSET: %d]",IR[11:9],IR[8:0]);
  `BR: $display($time, "ps [DECODE][OPCODE: BR][NZP: %b][PCOFFSET: %d]",IR[11:9],IR[8:0]);
  `JMP: $display($time, "ps [DECODE][OPCODE: JMP][BASE_R: R%d]",IR[8:6]);
  default: $display($time, "ps  [DECODE] ERROR: invalid opcode generated.");
  endcase
endfunction



task golden_ref_update();
//@(posedge clock);
if(deif.reset)
  begin
  	golden_ref.npc_out = 16'h0000;
  	golden_ref.IR = 16'h0000;
  	golden_ref.E_Control = 6'd0;
  	golden_ref.W_Control = 2'd0;
  	golden_ref.Mem_Control = 1'd0;
  end
else
  begin
	if(deif.enable_decode)
	  begin
	  	golden_ref.IR = deif.Instr_dout;
	  	golden_ref.npc_out = deif.npc_in;
		//W_Control
		if((deif.Instr_dout[15:12]==`ADD)||(deif.Instr_dout[15:12]==`AND)||(deif.Instr_dout[15:12]==`NOT)||(deif.Instr_dout[15:12]==`BR)||(deif.Instr_dout[15:12]==`JMP)||(deif.Instr_dout[15:12]==`ST)||(deif.Instr_dout[15:12]==`STR)||(deif.Instr_dout[15:12]==`STI))
			golden_ref.W_Control = 2'd0;
		else if((deif.Instr_dout[15:12]==`LD)||(deif.Instr_dout[15:12]==`LDR)||(deif.Instr_dout[15:12]==`LDI))
			golden_ref.W_Control = 2'd1;
		else if(deif.Instr_dout[15:12]==`LEA)
			golden_ref.W_Control = 2'd2;
		else 
			golden_ref.W_Control = 2'd0;

		//Mem_Control(Assuming that the unknown in zero according to the table???????)
		if((deif.Instr_dout[15:12]==`ADD)||(deif.Instr_dout[15:12]==`AND)||(deif.Instr_dout[15:12]==`NOT)||(deif.Instr_dout[15:12]==`LD)||(deif.Instr_dout[15:12]==`LDR)||(deif.Instr_dout[15:12]==`ST)||(deif.Instr_dout[15:12]==`STR)||(deif.Instr_dout[15:12]==`LEA)||(deif.Instr_dout[15:12]==`BR)||(deif.Instr_dout[15:12]==`JMP))
			golden_ref.Mem_Control = 1'd0;
		else if((deif.Instr_dout[15:12]==`LDI)||(deif.Instr_dout[15:12]==`STI))
			golden_ref.Mem_Control = 1'd1;
		else
			golden_ref.Mem_Control = 1'd0;


		//E_Control
		if((deif.Instr_dout[15:12]==`BR)||(deif.Instr_dout[15:12]==`LD)||(deif.Instr_dout[15:12]==`ST)||(deif.Instr_dout[15:12]==`LDI)||(deif.Instr_dout[15:12]==`STI)||(deif.Instr_dout[15:12]==`LEA))
			golden_ref.E_Control = 6'd6;
		else if((deif.Instr_dout[15:12]==`LDR)||(deif.Instr_dout[15:12]==`STR))
			golden_ref.E_Control = 6'd8;
		else if(deif.Instr_dout[15:12]==`JMP)
			golden_ref.E_Control = 6'd12;
		else if(deif.Instr_dout[15:12]==`NOT)
			golden_ref.E_Control = 6'd32;
		else if(deif.Instr_dout[15:12]==`ADD)
			begin
					if(deif.Instr_dout[5])
						golden_ref.E_Control= 6'd0;
					else
						golden_ref.E_Control= 6'd1;								
			end
		else if(deif.Instr_dout[15:12]==`AND)
			begin
					if(deif.Instr_dout[5])
						golden_ref.E_Control= 6'd16;
					else
						golden_ref.E_Control= 6'd17;
			end
		else 
				golden_ref.E_Control = 6'd0;
	  end
				
end
				
	endtask

	function golden_ref_chk();
			
	                if(golden_ref.W_Control != deif.W_Control)
	                begin
					$display($time, "[TB][DECODE][W_Control]:[Value from DUT: %b][Value from GR: %b]",deif.W_Control, golden_ref.W_Control);
					decode_err++;
	                end
	                if(golden_ref.E_Control != deif.E_Control)
	                begin
					$display($time, "[TB][DECODE][E_Control]:[Value from DUT: %b][Value from GR: %b]",deif.E_Control, golden_ref.E_Control);
	                decode_err++;
				    end
					
	                if(golden_ref.Mem_Control != deif.Mem_Control)
	                begin
					$display($time, "[TB][DECODE][MEM_Control]:[Value from DUT: %b][Value from GR: %b]",deif.Mem_Control, golden_ref.Mem_Control);
	                decode_err++;
					end
					
	                if(golden_ref.npc_out != deif.npc_out)
	                begin
	                $display($time, "[TB][DECODE][NPC_OUT]:[Value from DUT: %h][Value from GR: %h]",deif.npc_out, golden_ref.npc_out);
	                decode_err++;
					end
					
	                if(golden_ref.IR != deif.IR)
	                begin
					$display($time, "[TB][DECODE][IR]:[Value from DUT: %b][Value from GR: %b]",deif.IR, golden_ref.IR);                      
	                decode_err++;
					end

	endfunction

	task print_decode_err();
		$display("========================================================");
		$display("Decode Golden Reference: ");
		$display("IR: %b", golden_ref.IR);
		$display("E_Control: %b", golden_ref.E_Control);
		$display("NPC_OUT: %h", golden_ref.npc_out);
		$display("MEM_Control: %b", golden_ref.Mem_Control);
		$display("W_Control: %b", golden_ref.W_Control);
		$display("========================================================");
		$display("DUT Decode Outputs: ");
		$display("npc_in: %h",deif.npc_in);
		$display("enable_decode: %b",deif.enable_decode);
		$display("Instr_dout: %b",deif.Instr_dout);
		$display("IR: %b",deif.IR);
		$display("E_Control: %b", deif.E_Control);
		$display("npc_out: %h", deif.npc_out);
		$display("Mem_Control: %b", deif.Mem_Control);
		$display("W_Control: %b", deif.W_Control);
	endtask
 
endclass



