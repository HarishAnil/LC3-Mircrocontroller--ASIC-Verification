`timescale 1ns/1ps
`include "macros.sv"
import verif_classes::*;
module top();

bit clock=0;

logic reset;
logic [15:0] pc;
logic instrmem_rd, complete_instr, complete_data;
logic [15:0] Data_din, Data_addr, Data_dout;
logic Data_rd;
logic [15:0] INSTR;
int i, err_count;
logic [3:0] opcode_prev;

//=================================================
	LC3 LC3_DUT(	
	.clock(clock), 
	.reset(reset), 
	.pc(pc), 
	.instrmem_rd(instrmem_rd), 
	.Instr_dout(INSTR), 
	.Data_addr(Data_addr), 
	.complete_instr(complete_instr), 
	.complete_data(complete_data),  
	.Data_din(Data_din), 
	.Data_dout(Data_dout), 
	.Data_rd(Data_rd));
	
//==================================================
executeInterface exeInf(
//Input to the DUT
	.enable_execute(LC3_DUT.Ex.enable_execute), 
	.clock(clock), 
	.reset(reset), 
	.E_Control(LC3_DUT.Ex.E_Control), 
	.bypass_alu_1(LC3_DUT.Ex.bypass_alu_1),
	.bypass_alu_2(LC3_DUT.Ex.bypass_alu_2), 
	.bypass_mem_1(LC3_DUT.Ex.bypass_mem_1), 
	.bypass_mem_2(LC3_DUT.Ex.bypass_mem_2), 
	.IR(LC3_DUT.Ex.IR), 
	.npc_in(LC3_DUT.Ex.npc), 
	.W_Control_in(LC3_DUT.Ex.W_Control_in),
	.Mem_Control_in(LC3_DUT.Ex.Mem_Control_in),
	.VSR1(LC3_DUT.Ex.VSR1), 
	.VSR2(LC3_DUT.Ex.VSR2),
	.Mem_Bypass_Val(LC3_DUT.Ex.Mem_Bypass_Val),

//output from the DUT
	.dr(LC3_DUT.Ex.dr), 
	.sr1(LC3_DUT.Ex.sr1), 
	.sr2(LC3_DUT.Ex.sr2), 
	.W_Control_out(LC3_DUT.Ex.W_Control_out), 
	.Mem_Control_out(LC3_DUT.Ex.Mem_Control_out), 
	.aluout(LC3_DUT.Ex.aluout), 
	.pcout(LC3_DUT.Ex.pcout),
	.M_Data(LC3_DUT.Ex.M_Data), 
	.NZP(LC3_DUT.Ex.NZP), 
	.IR_Exec(LC3_DUT.Ex.IR_Exec),
	.aluin1(LC3_DUT.Ex.aluin1),
	.aluin2(LC3_DUT.Ex.aluin2));
//==================================================
	fetchInterface fetInf(
	.clock(clock), 
    .reset(reset), 
	.enable_updatePC(LC3_DUT.Fetch.enable_updatePC), 
	.enable_fetch(LC3_DUT.Fetch.enable_fetch), 
	.br_taken(LC3_DUT.Fetch.br_taken), 
	.instrmem_rd(LC3_DUT.Fetch.instrmem_rd), 
	.taddr(LC3_DUT.Fetch.taddr), 
	.pc(LC3_DUT.Fetch.pc), 
	.npc(LC3_DUT.Fetch.npc_out) );
//====================================================	
	decodeInterface decInf (
	.clock(clock), 
	.reset(reset), 
	.npc_in(LC3_DUT.Dec.npc_in), 
	.enable_decode(LC3_DUT.Dec.enable_decode), 
	.Instr_dout(LC3_DUT.Dec.dout), 
	.IR(LC3_DUT.Dec.IR), 
	.E_Control(LC3_DUT.Dec.E_Control), 
	.npc_out(LC3_DUT.Dec.npc_out), 
	.Mem_Control(LC3_DUT.Dec.Mem_Control), 
	.W_Control(LC3_DUT.Dec.W_Control));
//======================================================

	writebackInterface wbInf(
	.clock(clock), 
	.reset(reset), 
	.enable_writeback(LC3_DUT.WB.enable_writeback), 
	.aluout(LC3_DUT.WB.aluout), 
	.memout(LC3_DUT.WB.memout), 
	.pcout(LC3_DUT.WB.pcout), 
	.npc(LC3_DUT.WB.npc), 
	.VSR1(LC3_DUT.WB.d1), 
	.VSR2(LC3_DUT.WB.d2),
	.sr1(LC3_DUT.WB.sr1), 
	.sr2(LC3_DUT.WB.sr2), 
	.dr(LC3_DUT.WB.dr),
	.psr(LC3_DUT.WB.psr),
	.W_Control(LC3_DUT.WB.W_Control));
//====================================================
	memaccessInterface memInf(
	.mem_state(LC3_DUT.MemAccess.mem_state), 
	.M_Control(LC3_DUT.MemAccess.M_Control), 
	.DMem_rd(LC3_DUT.MemAccess.Data_rd),
	.DMem_din(LC3_DUT.MemAccess.Data_din),
	.M_Addr(LC3_DUT.MemAccess.M_Addr), 
	.DMem_dout(LC3_DUT.MemAccess.Data_dout), 
	.DMem_addr(LC3_DUT.MemAccess.Data_addr),
	.memout(LC3_DUT.MemAccess.memout),
	.M_Data(LC3_DUT.MemAccess.M_Data));
//=====================================================
	controlInterface cntrlInf(
	.clock(clock), 
	.reset(reset),
	.complete_data(LC3_DUT.Ctrl.complete_data), 
	.complete_instr(LC3_DUT.Ctrl.complete_instr), 
	.br_taken(LC3_DUT.Ctrl.br_taken), 
	.IR(LC3_DUT.Ctrl.IR), 
	.IR_Exec(LC3_DUT.Ctrl.IR_Exec),
	.IMem_dout(LC3_DUT.Ctrl.Instr_dout),
	.psr(LC3_DUT.Ctrl.psr),
	.NZP(LC3_DUT.Ctrl.NZP), 
	.bypass_alu_1(LC3_DUT.Ctrl.bypass_alu_1),
	.bypass_alu_2(LC3_DUT.Ctrl.bypass_alu_2),
	.bypass_mem_1(LC3_DUT.Ctrl.bypass_mem_1), 
	.bypass_mem_2(LC3_DUT.Ctrl.bypass_mem_2),
	.enable_fetch(LC3_DUT.Ctrl.enable_fetch),
	.enable_decode(LC3_DUT.Ctrl.enable_decode), 
	.enable_execute(LC3_DUT.Ctrl.enable_execute),
	.enable_writeback(LC3_DUT.Ctrl.enable_writeback),
	.enable_updatePC(LC3_DUT.Ctrl.enable_updatePC),
	.mem_state(LC3_DUT.Ctrl.mem_state));
//======================================================
	
always #5 clock=~clock;

initial 
	begin
		create_objects();
		resetfn();
		init_reg();
	
		for(i=0; i<=`num_sims; i++) begin
			@(posedge clock);
			drive_DUT();
			print_instructions();
			drive.start_driver();
			drive.update_scoreboard();
			if( i > 1000 && i < 100000) begin
				IR_Instmem.data_constraints.constraint_mode(1);
		end
		else
			IR_Instmem.data_constraints.constraint_mode(0);
		end
		drive.report_scoreboard();
	$finish;
	end	

task print_instructions();
	$display($time, "--InstructionMemory--");
IR_print(cntrlInf.IMem_dout);
	$display($time, "--Instruction_Decode--");
IR_print(cntrlInf.IR);
	$display($time, "--Instruction_Execute--");
IR_print(cntrlInf.IR_Exec);
endtask

function void IR_print(logic [15:0] IR);
	case(IR[15:12])
  `ADD: begin
    if(IR[5])
	 $display($time, "ps [Controller][OPCODE: IMMEDIATE ADD][DR: R%d][SR1: R%d][Imm5 value: %d]",IR[11:9],IR[8:6], IR[4:0]);
	else
	 $display($time, "ps [Controller][OPCODE: ADD][DR: R%d][SR: R%d][SR2: R%d]",IR[11:9],IR[8:6], IR[2:0]);
  end
  `AND: begin
    if(IR[5])
	 $display($time, "ps [Controller][OPCODE: IMMEDIATE AND][DR: R%d][SR1: R%d][Imm5 value: %d]",IR[11:9],IR[8:6], IR[4:0]);
	else
	 $display($time, "ps [Controller][OPCODE: AND][DR: R%d][SR: R%d][SR2: R%d]",IR[11:9],IR[8:6], IR[2:0]);
  end
  `NOT: $display($time, "ps [Controller][OPCODE: NOT][DR: R%d][SR1: R%d]",IR[11:9],IR[8:6]);
  `LD: $display($time, "ps [Controller][OPCODE: LD][DR: R%d][PCOFFSET: %d]",IR[11:9],IR[8:0]);
  `LDR: $display($time, "ps [Controller][OPCODE: LDR][DR: R%d][BASE_R: R%d][PCOFFSET: %d]",IR[11:9],IR[8:6],IR[5:0]);
  `LDI: $display($time, "ps [Controller][OPCODE: LDI][DR: R%d][PCOFFSET: %d]",IR[11:9],IR[8:0]);
  `LEA: $display($time, "ps [Controller][OPCODE: LEA][DR: R%d][PCOFFSET: %d]",IR[11:9],IR[8:0]);
  `ST: $display($time, "ps [Controller][OPCODE: ST][SR: R%d][PCOFFSET: %d]",IR[11:9],IR[8:0]);
  `STR: $display($time, "ps [Controller][OPCODE: STR][SR: R%d][BASE_R: R%d][PCOFFSET: %d]",IR[11:9], IR[8:6],IR[5:0]);
  `STI: $display($time, "ps [Controller][OPCODE: STI][SR: R%d][PCOFFSET: %d]",IR[11:9],IR[8:0]);
  `BR: $display($time, "ps [Controller][OPCODE: BR][NZP: %b][PCOFFSET: %d]",IR[11:9],IR[8:0]);
  `JMP: $display($time, "ps [Controller][OPCODE: JMP][BASE_R: R%d]",IR[8:6]);
  default: $display($time, "ps  [Controller] ERROR: invalid opcode generated: %b", IR[15:12]);
  endcase
endfunction

task resetfn();
	IR_Instmem.control_inst_counter = 5;
	IR_Instmem.mem_inst_counter = 5;
	err_count=0;
	reset=1'b1;
	complete_data=1'b0;
	complete_instr=1'b0;
	#10 reset=1'b0;
endtask	


task init_reg();
		//Initialize R0-R7 to 0
		for(i=0; i<=8; i++) begin
		    IR_Instmem.initialize_rf(i);
			complete_instr=1'b1;
			INSTR=IR_Instmem.IR;
			@(posedge clock);
		 end
		INSTR=16'dx;
		IR_Instmem.IR=16'dx;
		#100;
endtask


task drive_DUT();
			$display($time, "==================");
			$display($time, "Curent PC:%h", pc);
			IR_Instmem.randomize();
			Data_dout=IR_Instmem.Data_dout;
			complete_data = 1'b1;			
			IR_Instmem.Instr_pack(instrmem_rd);
			INSTR=IR_Instmem.IR;
endtask;


task create_objects();
	IR_Instmem=new();
	fet=new(fetInf);
	dec=new(decInf);
	write_back=new(wbInf);
	mem_a = new(memInf);
	cntrl = new(cntrlInf);
	exe = new(exeInf);
	drive = new(write_back, mem_a, dec, fet, cntrl, exe);
	alu_cover = new();
	mem_cover = new();
	ctrl_cover=new();
	opr_seq_cover=new();
endtask	

endmodule
