`include "macros.sv"

interface fetchInterface(
input logic clock, 
input logic reset, 
input logic enable_updatePC, 
input logic enable_fetch, 
input logic br_taken, 
input logic instrmem_rd, 
input logic [15:0] taddr, 
input logic [15:0] pc, 
input logic [15:0] npc );

property lC3_rst_fet;
	@(posedge clock)
	reset |-> ##1 (pc == 16'h3000);
endproperty

assert property (lC3_rst_fet);
cover property (lC3_rst_fet);

endinterface: fetchInterface

interface decodeInterface (
input logic clock, 
input logic reset, 
input logic [15:0] npc_in , 
input logic enable_decode, 
input logic [15:0] Instr_dout, 
input logic [15:0] IR, 
input logic [5:0] E_Control, 
input logic [15:0] npc_out, 
input logic Mem_Control, 
input logic [1:0] W_Control );

property LC3_rst_dec;
	@(posedge clock)
	reset |-> ##1 (!((Mem_Control)||(W_Control)||(E_Control)||(IR)||(npc_out)));
endproperty

assert property (LC3_rst_dec);
cover property (LC3_rst_dec);

endinterface: decodeInterface

interface executeInterface (

//Input to the DUT
input logic enable_execute, 
input logic clock, 
input logic reset, 
input logic [5:0] E_Control, 
input logic bypass_alu_1,
input logic bypass_alu_2, 
input logic bypass_mem_1, 
input logic bypass_mem_2, 
input logic [15:0] IR, 
input logic [15:0] npc_in, 
input logic [1:0] W_Control_in,
input logic Mem_Control_in,
input logic [15:0] VSR1, 
input logic [15:0] VSR2,
input logic [15:0] Mem_Bypass_Val,

 
//output from the DUT
input logic [2:0] dr, 
input logic [2:0] sr1, 
input logic [2:0] sr2, 
input logic [1:0] W_Control_out, 
input logic Mem_Control_out, 
input logic [15:0] aluout, 
input logic [15:0] pcout,
input logic [15:0] M_Data, 
input logic [2:0] NZP, 
input logic [15:0] IR_Exec,

//ALU ADDITIONS
input logic [15:0] aluin1, 
input logic [15:0] aluin2);



endinterface : executeInterface

interface writebackInterface (
input logic clock, reset, enable_writeback, 
input logic [15:0] aluout, memout, pcout, npc, VSR1, VSR2,
input logic [2:0] sr1, sr2, dr, psr,
input logic [1:0] W_Control);

//Output: VSR1, VSR2, PSR.	

property lC3_rst_wb;
	@(posedge clock)
	reset |-> ##1 (!psr);
endproperty
assert property (lC3_rst_wb);
cover property (lC3_rst_wb);
			
endinterface : writebackInterface

interface memaccessInterface(
input logic [1:0] mem_state, 
input logic M_Control, DMem_rd ,
input logic [15:0] DMem_din, M_Addr, DMem_dout, DMem_addr, memout,M_Data );
	
//output: DMem_addr, DMem_rd, DMem_din(15:0), memout	
endinterface : memaccessInterface

interface controlInterface(
input logic clock, reset, complete_data, complete_instr, br_taken, 
input logic [15:0] IR, IR_Exec, IMem_dout,
input logic [2:0] psr, NZP, 
input logic bypass_alu_1, bypass_alu_2, bypass_mem_1, bypass_mem_2, enable_fetch, enable_decode, enable_execute, enable_writeback, enable_updatePC,
input logic [1:0] mem_state);

//Branch
property CTRL_br_taken_jmp;
	@(posedge clock)
	|(NZP & psr) |-> br_taken;
endproperty
		
		assert property (CTRL_br_taken_jmp); 
		cover property (CTRL_br_taken_jmp);

//Execute assertions
property CTRL_enable_execute_low1;
	@(posedge clock)
	(IR[15:12] == `ST || IR[15:12] == `STR  || IR[15:12] == `STI || IR[15:12] == `LD || IR[15:12] == `LDR || IR[15:12] == `LDI ) |=>  !enable_execute;
endproperty

property CTRL_enable_execute_low2;
	@(posedge clock)
	(IMem_dout[15:12] == `BR || IMem_dout[15:12] == `JMP) |=>  ##2 !enable_execute;
endproperty

cover property (CTRL_enable_execute_low1);
cover property (CTRL_enable_execute_low2);

property CTRL_enable_execute_high1;
	@(posedge clock)
	(IR[15:12] == `ST || IR[15:12] == `STR || IR[15:12] == `LD || IR[15:12] == `LDR ) |=>  ##1 enable_execute;
endproperty
property CTRL_enable_execute_high2;
	@(posedge clock)
	(IR[15:12] == `LDI || IR[15:12] == `STI ) |=>  ##2 enable_execute;
endproperty
property CTRL_enable_execute_high3;
	@(posedge clock)
	((IMem_dout[15:12] == `BR) || (IMem_dout[15:12] == `JMP)) |=>  ##5 enable_execute;
endproperty

assert property (CTRL_enable_execute_high1); 
cover property  (CTRL_enable_execute_high1);
assert property (CTRL_enable_execute_high2); 
cover property  (CTRL_enable_execute_high2);
//assert property (CTRL_enable_execute_high3); 
cover property  (CTRL_enable_execute_high3);

//Decode Assertions
property CTRL_enable_decode_low1;
	@(posedge clock)
	(IR[15:12] == `ST || IR[15:12] == `STR  || IR[15:12] == `STI || IR[15:12] == `LD || IR[15:12] == `LDR || IR[15:12] == `LDI ) |=>  !enable_decode;
endproperty

property CTRL_enable_decode_low2;
	@(posedge clock)
	(IMem_dout[15:12] == `BR || IMem_dout[15:12] == `JMP)  |=>  ##1 !enable_decode;
endproperty

cover property (CTRL_enable_decode_low1);
cover property (CTRL_enable_decode_low2);

property CTRL_enable_decode_high1;
	@(posedge clock)
	(IR[15:12] == `ST || IR[15:12] == `STR || IR[15:12] == `LD || IR[15:12] == `LDR ) |=>  ##1 enable_decode;
endproperty
property CTRL_enable_decode_high2;
	@(posedge clock)
	(IR[15:12] == `LDI || IR[15:12] == `STI ) |=>  ##2 enable_decode;
endproperty
property CTRL_enable_decode_high3;
	@(posedge clock)
	(IMem_dout[15:12] == `BR) || (IMem_dout[15:12] == `JMP) |=>  ##4 enable_decode;
endproperty

//assert property (CTRL_enable_decode_high1); 
cover property  (CTRL_enable_decode_high1);
//assert property (CTRL_enable_decode_high2); 
cover property  (CTRL_enable_decode_high2);
//assert property (CTRL_enable_decode_high3); 
cover property  (CTRL_enable_decode_high3);

//Fetch
property CTRL_enable_fetch_low;
	@(posedge clock)
	(IR[15:12] == `ST || IR[15:12] == `STR  || IR[15:12] == `STI || IR[15:12] == `LD || IR[15:12] == `LDR || IR[15:12] == `LDI || IMem_dout[15:12] == `BR || IMem_dout[15:12] == `JMP) |=>  !enable_fetch;
endproperty

cover property (CTRL_enable_fetch_low);

property CTRL_enable_fetch_high1;
	@(posedge clock)
	(IR[15:12] == `ST || IR[15:12] == `STR || IR[15:12] == `LD || IR[15:12] == `LDR ) |=>  ##1 enable_fetch;
endproperty
property CTRL_enable_fetch_high2;
	@(posedge clock)
	(IR[15:12] == `LDI || IR[15:12] == `STI ) |=>  ##2 enable_fetch;
endproperty
property CTRL_enable_fetch_high3;
	@(posedge clock)
	(IMem_dout[15:12] == `BR) || (IMem_dout[15:12] == `JMP) |=>  ##3 enable_fetch;
endproperty

//assert property (CTRL_enable_fetch_high1); 
cover property (CTRL_enable_fetch_high1);
//assert property (CTRL_enable_fetch_high2); 
cover property (CTRL_enable_fetch_high2);
//assert property (CTRL_enable_fetch_high3); 
cover property (CTRL_enable_fetch_high3);


//----------------------Wriback block enable-----------------------//

		property CTRL_enable_writeback_Load;
			@(posedge clock)
			(IR[15:12] == `LD || IR[15:12] == `LDR ) |=>  ##1 enable_writeback;
		endproperty
		
		
		property CTRL_enable_writeback_Brn;
			@(posedge clock)
			(IMem_dout[15:12] == `BR) || (IMem_dout[15:12] == `JMP) |=>  ##6 enable_writeback;
		endproperty
		
		assert property (CTRL_enable_writeback_Load); 
		cover property  (CTRL_enable_writeback_Load);
		//assert property (CTRL_enable_writeback_Brn); 
		cover property  (CTRL_enable_writeback_Brn);

				
		property CTRL_enable_wb_ST1;
		@(posedge clock)
		(IR_Exec[15:12]==`STR || IR_Exec[15:12]==`ST || IR_Exec[15:12]==`STI) |-> enable_writeback==1'b0;
		endproperty
	
		property CTRL_enable_wb_ST2;
		@(posedge clock)
		(IR_Exec[15:12]==`STR || IR_Exec[15:12]==`ST) |=> enable_writeback==1'b1;
		endproperty
	
		property CTRL_enable_wb_ST3;
		@(posedge clock)
		(IR_Exec[15:12]==`STI) ##3 enable_writeback==1'b1;
		endproperty
		
		assert property (CTRL_enable_wb_ST1);
		cover property  (CTRL_enable_wb_ST1);
		//assert property (CTRL_enable_wb_ST2);
		cover property  (CTRL_enable_wb_ST2);
		//assert property (CTRL_enable_wb_ST3);
		cover property  (CTRL_enable_wb_ST3);
		





		//---------------Asserting all bypass signals for all combination----------------// 
		// Refer the controls test block if the IR_Ex and IR Dest and Source match flag the bypass accordingly.
		// Not all combination in testbench covered here, only those mentioned in coverage plan.
		// No Control signals asserted here
		
		property CTRL_bypass_alu_1_AA; // ALU after ALU instruction (Removed LEA)
			@(posedge clock)
		((IR[15:12] == `ADD) || (IR[15:12] == `AND) || (IR[15:12] == `NOT)) && ((IR_Exec[15:12] == `ADD) || (IR_Exec[15:12] == `AND) || (IR_Exec[15:12] == `NOT) /*|| (IR_Exec[15:12] == `LEA)*/) && (IR_Exec[11:9] == IR[8:6]) |-> bypass_alu_1 == 1'b1;
		endproperty
		assert property (CTRL_bypass_alu_1_AA); 
		cover property  (CTRL_bypass_alu_1_AA);

		property CTRL_bypass_alu_2_AA; // ALU after ALU (Removed LEA)
			@(posedge clock)
		((IR[15:12] == `ADD) || (IR[15:12] == `AND) || (IR[15:12] == `NOT)) 
		&& ((IR_Exec[15:12] == `ADD) || (IR_Exec[15:12] == `AND) || (IR_Exec[15:12] == `NOT)/*|| (IR_Exec[15:12] == `LEA)*/) 
		&& ((IR_Exec[11:9] == IR[2:0]) && (IR[5] == 1'b0)) |-> bypass_alu_2 == 1'b1;
		endproperty
		assert property (CTRL_bypass_alu_2_AA); 
		cover property  (CTRL_bypass_alu_2_AA);
		
				
		property CTRL_bypass_alu_1_AS; // ALU and store (I have added STR, ST, STI)
			@(posedge clock)
		((IR_Exec[15:12] == `ADD) || (IR_Exec[15:12] == `AND) || (IR_Exec[15:12] == `NOT)) 
		  && ((IR[15:12] == `STR)/*||(IR[15:12] == `ST)||(IR[15:12] == `STI)*/) 
		  && (IR_Exec[11:9] == IR[8:6]) |-> bypass_alu_1 == 1'b1;
		endproperty
		assert property (CTRL_bypass_alu_1_AS); 
		cover property  (CTRL_bypass_alu_1_AS);
		
		
		property CTRL_bypass_alu_2_AS; // ALU and store (have excluded LEA) (Base register is a source)
		@(posedge clock)
		((IR_Exec[15:12] == `ADD) || (IR_Exec[15:12] == `AND) || (IR_Exec[15:12] == `NOT)) 
			&& ((IR[15:12] == `STR)||(IR[15:12] == `ST)||(IR[15:12] == `STI)) 
		 && (IR_Exec[11:9] == IR[11:9]) |-> bypass_alu_2 == 1'b1;
		endproperty
		assert property (CTRL_bypass_alu_2_AS); 
		cover property  (CTRL_bypass_alu_2_AS);
		
		
		property CTRL_bypass_alu_1_AL;  //(this should be der)
		@(posedge clock)
		((IR_Exec[15:12] == `ADD) || (IR_Exec[15:12] == `AND) || (IR_Exec[15:12] == `NOT)) && (IR[15:12] == `LDR) && (IR_Exec[11:9] == IR[8:6]) |-> bypass_alu_1 == 1'b1;
		endproperty
		assert property (CTRL_bypass_alu_1_AL); 
		cover property  (CTRL_bypass_alu_1_AL);
		
		//----------------------------bypass_mem line assertions--------------------.
		
		property CTRL_bypass_mem_1_LA;
			@(posedge clock)
		((IR_Exec[15:12] == `LD) || (IR_Exec[15:12] == `LDR) || (IR_Exec[15:12] == `LDI)) && ((IR[15:12] == `ADD) || (IR[15:12] == `AND) || (IR[15:12] == `NOT)) && (IR_Exec[11:9] == IR[8:6]) |-> bypass_mem_1 == 1'b1;
		endproperty
		assert property (CTRL_bypass_mem_1_LA); 
		cover property  (CTRL_bypass_mem_1_LA);

		property CTRL_bypass_mem_2_LA;
			@(posedge clock)
		((IR_Exec[15:12] == `LD) || (IR_Exec[15:12] == `LDR) || (IR_Exec[15:12] == `LDI)) && ((IR[15:12] == `ADD) || (IR[15:12] == `AND) || (IR[15:12] == `NOT)) && ((IR_Exec[11:9] == IR[2:0]) && (IR[5] == 1'b0)) |-> bypass_mem_2 == 1'b1;
		endproperty
		assert property (CTRL_bypass_mem_2_LA); 
		cover property  (CTRL_bypass_mem_2_LA);
		
		
		// LS is not a possible assertion or a coverage parametre since the DUT has a constrains in its operation, that no two mem or control will be in pipeline simultaneously.
		
		// property CTRL_bypass_mem_1_LS;
		// @(posedge clock)
		// ((IR_Exec[15:12] == `LD) || (IR_Exec[15:12] == `LDR) || (IR_Exec[15:12] == `LDI)) && ((IR[15:12] == `STR) || (IR[15:12] == `ST) || (IR[15:12] == `STI))  && (IR_Exec[11:9] == IR[11:9])|-> bypass_mem_2 == 1'b1;
		// endproperty
		// assert property (CTRL_bypass_mem_1_LS); 
		// cover property  (CTRL_bypass_mem_1_LS);
				
		
		// property CTRL_bypass_mem_2_LS;
			// @(posedge clock)
		// ((IR_Exec[15:12] == `LD) || (IR_Exec[15:12] == `LDR) || (IR_Exec[15:12] == `LDI)) && (IR[15:12] == `STR) && (IR_Exec[11:9] == IR[8:6])|-> bypass_mem_2 == 1'b1;
		// endproperty
		// assert property (CTRL_bypass_mem_2_LS); 
		// cover property  (CTRL_bypass_mem_2_LS);
		
		
		//-------------- mem state changes assertions, refer the spec sheet FSM table, control block is more confusing ------//
		
		
		property CTRL_mem_state_LDI;
			@(posedge clock)
			(IR[15:12] == `LDI) |=>  mem_state == 2'b01 ##1 mem_state == 2'b00 ##1 mem_state == 2'b11;
		endproperty
		assert property (CTRL_mem_state_LDI); 
		cover property  (CTRL_mem_state_LDI);

		property CTRL_mem_state_STI;
			@(posedge clock)
			(IR[15:12] == `STI) |=>  mem_state == 2'b01 ##1 mem_state == 2'b10 ##1 mem_state == 2'b11;
		endproperty
		assert property (CTRL_mem_state_STI); 
		cover property  (CTRL_mem_state_STI);

	
	
		property CTRL_enable_mem_state_ST_STR;
			@(posedge clock)
			(IR[15:12] == `ST || IR[15:12] == `STR ) |=>  mem_state == 2'b10 ##1 mem_state == 2'b11;
		endproperty
		assert property (CTRL_enable_mem_state_ST_STR); 
		cover property  (CTRL_enable_mem_state_ST_STR);
		
		property CTRL_enable_mem_state_STI_LDI;
		@(posedge clock)
		(IR[15:12] == `LDI || IR[15:12] == `STI ) |=>  mem_state == 2'b01 ##2 mem_state == 2'b11;
		endproperty
		assert property (CTRL_enable_mem_state_STI_LDI); 
		cover property  (CTRL_enable_mem_state_STI_LDI);
		
		
		property CTRL_enable_mem_state_LD_LDR;
			@(posedge clock)
			(IR[15:12] == `LD || IR[15:12] == `LDR ) |=>  mem_state == 2'b00 ##1 mem_state == 2'b11;
		endproperty
		assert property (CTRL_enable_mem_state_LD_LDR); 
		cover property  (CTRL_enable_mem_state_LD_LDR);
		
		
		// -------------------- Mem State Transitions ---------------------------//

		property CTRL_mem_state_3_1;
			@(posedge clock)
			(mem_state == 2'b11) && ((IR[15:12] == `LDI) || (IR[15:12] == `LDI)) |=>  mem_state == 2'b01;
		endproperty
		assert property (CTRL_mem_state_3_1); 
		cover property  (CTRL_mem_state_3_1);

		property CTRL_mem_state_3_0;
			@(posedge clock)
			(mem_state == 2'b11) && (IR[15:12] == `LDI) |=>  mem_state == 2'b01 ##1 mem_state == 2'b00;
		endproperty
		assert property (CTRL_mem_state_3_0); 
		cover property  (CTRL_mem_state_3_0);

		property CTRL_mem_state_3_2;
			@(posedge clock)
			(mem_state == 2'b11) && (IR[15:12] == `STI) |=>  mem_state == 2'b01 ##1 mem_state == 2'b10;
		endproperty
		assert property (CTRL_mem_state_3_2); 
		cover property  (CTRL_mem_state_3_2);

		property CTRL_mem_state_2_3;
			@(posedge clock)
			(mem_state == 2'b10) && (complete_data == 1) |=>  mem_state == 2'b11;
		endproperty
		assert property (CTRL_mem_state_2_3); 
		cover property  (CTRL_mem_state_2_3);

		property CTRL_mem_state_0_3;
			@(posedge clock)
			(mem_state == 2'b00) && (complete_data == 1) |=>  mem_state == 2'b11;
		endproperty
		assert property (CTRL_mem_state_0_3); 
		cover property  (CTRL_mem_state_0_3);

		property CTRL_mem_state_1_2;
			@(posedge clock)
			(mem_state == 2'b01) && (IR_Exec[15:12] == `STI) |=>  mem_state == 2'b10;
		endproperty
		assert property (CTRL_mem_state_1_2); 
		cover property  (CTRL_mem_state_1_2);

		property CTRL_mem_state_1_0;
			@(posedge clock)
			(mem_state == 2'b01) && (IR_Exec[15:12] == `LDI) |=>  mem_state == 2'b00;
		endproperty
		assert property (CTRL_mem_state_1_0); 
		cover property  (CTRL_mem_state_1_0);

		property CTRL_enable_writeback_STR_fall1;
			@(posedge clock)
			(IR[15:12] == `ST || IR[15:12] == `STR || IR[15:12] == `LD || IR[15:12] == `LDR || IR[15:12] == `LDI || IR[15:12] == `STI ) |=>  !enable_writeback;
		
		endproperty
		property CTRL_enable_writeback_BR_fall2;
			@(posedge clock)
			(IMem_dout[15:12] == `BR || IMem_dout[15:12] == `JMP) |=>  ##2 !enable_writeback;
		
		endproperty
		
		cover property (CTRL_enable_writeback_STR_fall1);
		cover property (CTRL_enable_writeback_BR_fall2);
		
		
		
		
		
endinterface : controlInterface

interface topInterface(input bit clock);
  	
	
  	
endinterface : topInterface
