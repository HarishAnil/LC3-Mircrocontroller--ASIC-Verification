//=================================================================
// ECE 745 ASIC Verification
// Final Project: LC3 Microprocessor Verification
//=================================================================
`include "macros.sv"
covergroup ALU_OPR_cg @(posedge dec.deif.clock);
	Cov_alu_opcode: coverpoint dec.golden_ref.IR[15:12] {
		bins ADD_bin = {`ADD};
		bins AND_bin = {`AND};
		bins NOT_bin = {`NOT};
	}
	Cov_ADD_AND: coverpoint dec.golden_ref.IR[15:12] {
		bins ADD_p = {`ADD};
		bins AND_p = {`AND};
	}
	Cov_NOT: coverpoint dec.golden_ref.IR[15:12] {
		bins NOT_p = {`NOT};
	}
	Cov_imm_en: coverpoint dec.golden_ref.IR[5] iff((dec.golden_ref.IR[15:12] == `ADD) || (dec.golden_ref.IR[15:12] == `AND)) {
		bins H = {1'b1};
		bins L = {1'b0};
	}

	Cov_SR1: coverpoint dec.golden_ref.IR[8:6] {
		bins sr1_alu[]  = {[7:0]};
	}
	Cov_SR2: coverpoint dec.golden_ref.IR[2:0] {
		bins sr2_alu[]  = {[7:0]};
	}
	Cov_DR: coverpoint dec.golden_ref.IR[11:9] {
		bins dr_alu[]  = {[7:0]};
	}
	Cov_imm5: coverpoint dec.golden_ref.IR[4:0] iff((dec.golden_ref.IR[5] == 1'b1)&&((dec.golden_ref.IR[15:12] == `ADD) || (dec.golden_ref.IR[15:12] == `AND))){
		bins imm5_alu[]  = {[5'b00000: 5'b11111]};
	}

	Xc_opcode_imm_en: cross Cov_ADD_AND, Cov_imm_en;
	Xc_opcode_dr_sr1_imm5: cross Cov_ADD_AND, Cov_SR1, Cov_DR, Cov_imm5;
	Xc_opcode_dr_sr1_sr2: cross Cov_ADD_AND, Cov_SR1, Cov_DR, Cov_SR2 iff(dec.golden_ref.IR[5] == 1'b0);
  	Xc_opcode_dr_src1_not : cross Cov_NOT,Cov_SR1,Cov_DR;
	
	Cov_aluin1: coverpoint exe.exe_intf.aluin1{
		option.auto_bin_max = 8;
	}
	Cov_aluin1_corner: coverpoint exe.exe_intf.aluin1{
		bins aluin1_corner_high = {16'hffff};
		bins  aluin1_corner_low= {16'h0000};
	}
	Cov_aluin2: coverpoint exe.exe_intf.aluin2{
		option.auto_bin_max = 8;
	}
	Cov_aluin2_corner: coverpoint exe.exe_intf.aluin2{
		bins aluin2_corner_high = {16'hffff};
		bins  aluin2_corner_low= {16'h0000};
	}

	Xc_opcode_aluin1:cross Cov_alu_opcode, Cov_aluin1_corner;
	Xc_opcode_aluin2:cross Cov_alu_opcode, Cov_aluin2_corner;

	Cov_aluin1_zero: coverpoint exe.exe_intf.aluin1{	
		bins  aluin1_corner_low= {16'h0000};
	}
	Cov_aluin1_one: coverpoint exe.exe_intf.aluin1{	
		bins  aluin1_corner_high= {16'hffff};
	}
	Cov_aluin2_zero: coverpoint exe.exe_intf.aluin2{	
		bins  aluin2_corner_low= {16'h0000};
	}
	Cov_aluin2_one: coverpoint exe.exe_intf.aluin2{	
		bins  aluin2_corner_high= {16'hffff};
	}

	Cov_aluin1_alt10: coverpoint exe.exe_intf.aluin1{	
		bins  aluin1_alt_MSB0= {16'b0101010101010101};
	}
	Cov_aluin1_alt01: coverpoint exe.exe_intf.aluin1{	
		bins  aluin1_alt_MSB1= {16'b1010101010101010};
	}
	Cov_aluin2_alt10: coverpoint exe.exe_intf.aluin2{	
		bins  aluin2_alt_MSB0= {16'b0101010101010101};
	}
	Cov_aluin2_alt01: coverpoint exe.exe_intf.aluin2{	
		bins  aluin2_alt_MSB1= {16'b1010101010101010};
	}

	Cov_aluin1_pos: coverpoint exe.exe_intf.aluin1[15]{	
		bins  aluin1_pos= {1'b0};
	}

	Cov_aluin1_neg: coverpoint exe.exe_intf.aluin1[15]{	
		bins  aluin1_neg= {1'b1};
	}

	Cov_aluin2_pos: coverpoint exe.exe_intf.aluin2[15]{	
		bins  aluin2_pos= {1'b0};
	}

	Cov_aluin2_neg: coverpoint exe.exe_intf.aluin2[15]{	
		bins  aluin2_neg= {1'b1};
	}


	Cov_opr_zero_zero:cross Cov_aluin1_zero, Cov_aluin2_zero,Cov_alu_opcode{
	ignore_bins others = binsof (Cov_alu_opcode) intersect {`NOT};}

	Cov_opr_zero_all1:cross Cov_aluin1_zero, Cov_aluin2_one,Cov_alu_opcode{
	ignore_bins others = binsof (Cov_alu_opcode) intersect {`NOT};}

	Cov_opr_all1_zero:cross Cov_aluin1_one, Cov_aluin2_zero,Cov_alu_opcode{
	ignore_bins others = binsof (Cov_alu_opcode) intersect {`NOT};}

	Cov_opr_all1_all1:cross Cov_aluin1_one, Cov_aluin2_one,Cov_alu_opcode{
	ignore_bins others = binsof (Cov_alu_opcode) intersect {`NOT};}


	Cov_opr_alt01_alt01:cross Cov_aluin1_alt01, Cov_aluin2_alt01,Cov_alu_opcode{
	ignore_bins others = binsof (Cov_alu_opcode) intersect {`NOT};}

	Cov_opr_alt01_alt10:cross Cov_aluin1_alt01, Cov_aluin2_alt10,Cov_alu_opcode{
	ignore_bins others = binsof (Cov_alu_opcode) intersect {`NOT};}

	Cov_opr_alt10_alt01:cross Cov_aluin1_alt10, Cov_aluin2_alt01,Cov_alu_opcode{
	ignore_bins others = binsof (Cov_alu_opcode) intersect {`NOT};}

	Cov_opr_alt10_alt10:cross Cov_aluin1_alt10, Cov_aluin2_alt10,Cov_alu_opcode{
	ignore_bins others = binsof (Cov_alu_opcode) intersect {`NOT};}


	Cov_opr_pos_pos: cross Cov_aluin1_pos, Cov_aluin2_pos, Cov_alu_opcode{
	ignore_bins others = binsof (Cov_alu_opcode) intersect {`NOT};}

	Cov_opr_pos_neg: cross Cov_aluin1_pos, Cov_aluin2_neg, Cov_alu_opcode{
	ignore_bins others = binsof (Cov_alu_opcode) intersect {`NOT};}

	Cov_opr_neg_pos: cross Cov_aluin1_neg, Cov_aluin2_pos, Cov_alu_opcode{
	ignore_bins others = binsof (Cov_alu_opcode) intersect {`NOT};}

	Cov_opr_neg_neg: cross Cov_aluin1_neg, Cov_aluin2_neg, Cov_alu_opcode{
	ignore_bins others = binsof (Cov_alu_opcode) intersect {`NOT};}



endgroup


covergroup MEM_OPR_cg @(posedge dec.deif.clock);
  Cov_mem_opcode: coverpoint dec.golden_ref.IR[15:12] {
		bins LD_bins = {`LD};
		bins LDR_bins = {`LDR};
		bins LEA_bins = {`LEA};
		bins LDI_bins = {`LDI};
		bins ST_bins = {`ST};
		bins STR_bins = {`STR};
		bins STI_bins = {`STI};
	}
  Cov_BaseR_LDR: coverpoint dec.golden_ref.IR[8:6] iff(dec.golden_ref.IR[15:12] == `LDR) {
		bins LDR_base[] ={[3'b000:3'b111]}; 
  }
  Cov_BaseR_STR: coverpoint dec.golden_ref.IR[8:6] iff(dec.golden_ref.IR[15:12] == `STR) {
		bins STR_base[] ={[3'b000:3'b111]}; 
  }

  Cov_SR_ST: coverpoint dec.golden_ref.IR[11:9] iff(dec.golden_ref.IR[15:12] == `ST) {
		bins ST_source[] ={[3'b000:3'b111]}; 
  }
  Cov_SR_STI: coverpoint dec.golden_ref.IR[11:9] iff(dec.golden_ref.IR[15:12] == `STI) {
		bins STI_source[] ={[3'b000:3'b111]}; 
  }
  Cov_SR_STR: coverpoint dec.golden_ref.IR[11:9] iff(dec.golden_ref.IR[15:12] == `STR) {
		bins STR_source[] ={[3'b000:3'b111]}; 
  }


  Cov_DR_LD: coverpoint dec.golden_ref.IR[11:9] iff(dec.golden_ref.IR[15:12] == `LD) {
		bins LD_DR[] ={[3'b000:3'b111]}; 
  }
  Cov_DR_LDR: coverpoint dec.golden_ref.IR[11:9] iff(dec.golden_ref.IR[15:12] == `LDR) {
		bins LDR_DR[] ={[3'b000:3'b111]}; 
  }
  Cov_DR_LDI: coverpoint dec.golden_ref.IR[11:9] iff(dec.golden_ref.IR[15:12] == `LDI) {
		bins LDI_DR[] ={[3'b000:3'b111]}; 
  }
  Cov_DR_LEA: coverpoint dec.golden_ref.IR[11:9] iff(dec.golden_ref.IR[15:12] == `LEA) {
		bins LEA_DR[] ={[3'b000:3'b111]}; 
  }
  Cov_PCoffset9: coverpoint dec.golden_ref.IR[8:0] 
	iff(dec.golden_ref.IR[15:12] == `LD 
  ||dec.golden_ref.IR[15:12] == `LDI
  ||dec.golden_ref.IR[15:12] == `LEA
  ||dec.golden_ref.IR[15:12] == `ST
  ||dec.golden_ref.IR[15:12] == `STI
  ||dec.golden_ref.IR[15:12] == `BR){
		option.auto_bin_max = 8; 
  }

  Cov_PCoffset6: coverpoint dec.golden_ref.IR[5:0] 
	iff(dec.golden_ref.IR[15:12] == `LDR 
	||dec.golden_ref.IR[15:12] == `STR){
  option.auto_bin_max = 8; 
  }

  Cov_PCoffset9_c: coverpoint dec.golden_ref.IR[8:0] 
	iff(dec.golden_ref.IR[15:12] == `LD 
  ||dec.golden_ref.IR[15:12] == `LDI
  ||dec.golden_ref.IR[15:12] == `LEA
  ||dec.golden_ref.IR[15:12] == `ST
  ||dec.golden_ref.IR[15:12] == `STI
  ||dec.golden_ref.IR[15:12] == `BR){
		bins offset9_low_corner = {9'b000000000};
		bins offset9_high_corner = {9'b111111111};  
  }

  Cov_PCoffset6_c: coverpoint dec.golden_ref.IR[5:0] 
	iff(dec.golden_ref.IR[15:12] == `LDR 
	||dec.golden_ref.IR[15:12] == `STR){
		bins offset9_low_corner = {6'b000000};
		bins offset9_high_corner = {6'b111111};  
  }

	Xc_BaseR_SR_offset6: cross Cov_PCoffset6, Cov_SR_STR, Cov_BaseR_STR, Cov_mem_opcode{
	ignore_bins others = binsof (Cov_mem_opcode) intersect {`LD, `LDR, `LDI, `LEA, `ST, `STI};}

	Xc_BaseR_SR_offset6_c: cross Cov_PCoffset6_c, Cov_SR_STR, Cov_BaseR_STR, Cov_mem_opcode{
	ignore_bins others = binsof (Cov_mem_opcode) intersect {`LD, `LDR, `LDI, `LEA, `ST, `STI};}

	Xc_BaseR_DR_offset6: cross Cov_PCoffset6, Cov_DR_LDR, Cov_BaseR_LDR, Cov_mem_opcode{
	ignore_bins others = binsof (Cov_mem_opcode) intersect {`LD, `STR, `LDI, `LEA, `ST, `STI};}


	Xc_BaseR_DR_offset6_c: cross Cov_PCoffset6_c, Cov_DR_LDR, Cov_BaseR_LDR, Cov_mem_opcode{
	ignore_bins others = binsof (Cov_mem_opcode) intersect {`LD, `STR, `LDI, `LEA, `ST, `STI};}

endgroup


covergroup CTRL_OPR_cg @(posedge cntrl.CtrlInf.clock);
Cov_ctrl_opcode: coverpoint dec.golden_ref.IR[15:12]{
	bins BR_bins = {`BR};
	bins JMP_bins = {`JMP};}

Cov_BaseR: coverpoint dec.golden_ref.IR[8:6] iff(dec.golden_ref.IR[15:12] == `JMP) { 
 	bins JMP_BaseR[] = {[7:0]};
}
Cov_NZP: coverpoint exe.exe_gr_out.NZP[2:0] iff(dec.golden_ref.IR[15:12] ==`JMP) { 
 	bins JMP_NZP[] = {7};
}
Cov_PSR: coverpoint write_back.golden_ref.psr[2:0] iff(dec.golden_ref.IR[15:12] ==`JMP) { 
 	bins JMP_PSR4 = {3'b100};
	bins JMP_PSR2 = {3'b010};
        bins JMP_PSR1 = {3'b001};
}
Cov_PCoffset9: coverpoint dec.golden_ref.IR[8:0] iff(dec.golden_ref.IR[15:12] == `BR) {
	option.auto_bin_max = 8;
}
Cov_PCoffset9_c: coverpoint dec.golden_ref.IR[8:0] iff(dec.golden_ref.IR[15:12] == `BR) {
	bins offset9_low_corner = {9'b000000000};
	bins offset9_high_corner = {9'b111111111}; 
}
Xc_NZP_PSR: cross Cov_NZP, Cov_PSR;

endgroup

covergroup OPR_SEQ_cg @(posedge dec.deif.clock);	
Cov_opcode_order : coverpoint dec.golden_ref.IR[15:12]
{
	bins ALU_Memory = (`AND, `ADD, `NOT => `LD, `LDR, `LDI, `LEA, `ST, `STR, `STI);
	bins Memory_ALU = (`LD, `LDR, `LDI, `LEA,`ST, `STR, `STI => `AND, `ADD, `NOT);
	bins ALU_Control = (`AND, `ADD, `NOT => `BR, `JMP );
	bins Control_ALU = ( `BR, `JMP => `AND, `ADD, `NOT);
	bins Memory_Control = ( `LD, `LDR, `LDI, `LEA, `ST, `STR, `STI => `BR, `JMP);
	bins Control_Memory = ( `BR, `JMP => `LD, `LDR, `LDI, `LEA, `ST, `STR, `STI);		
}

Cov_opcode_ADD_others : coverpoint dec.golden_ref.IR[15:12]
	{
		//ADD --> ALU Operation
		bins ADD_AND = (`ADD => `AND);
		bins ADD_NOT = (`ADD => `NOT);
		bins ADD_ADD = (`ADD => `ADD);

		//ADD --> Load Instruction
		bins ADD_LD  = (`ADD => `LD);
		bins ADD_LDR = (`ADD => `LDR);
		bins ADD_LDI = (`ADD=> `LDI);
		bins ADD_LEA = (`ADD => `LEA);

 		//ADD --> Store Instruction
		bins ADD_ST  = (`ADD => `ST);
		bins ADD_STR = (`ADD => `STR);
		bins ADD_STI = (`ADD => `STI);

		//ADD --> Control Instruction
		bins ADD_BR  = (`ADD => `BR);
		bins ADD_JMP = (`ADD => `JMP);

	}

Cov_opcode_AND_others : coverpoint dec.golden_ref.IR[15:12]
	{
		//AND --> ALU Operation
		bins AND_ADD = (`AND => `ADD);
		bins AND_AND = (`AND => `AND);
		bins AND_NOT = (`AND => `NOT);

		//AND --> Load Instruction
		bins AND_LD  = (`AND => `LD);
		bins AND_LDR = (`AND => `LDR);
		bins AND_LDI = (`AND => `LDI);
		bins AND_LEA = (`AND => `LEA);

		//And --> Store Instruction
		bins AND_ST  = (`AND => `ST);
		bins AND_STR = (`AND => `STR);
		bins AND_STI = (`AND => `STI);

		//ADD --> Control Instruction
		bins AND_BR  = (`AND => `BR);
		bins AND_JMP = (`AND => `JMP);

	}

Cov_opcode_NOT_others : coverpoint dec.golden_ref.IR[15:12] 
	{
		//NOT --> ALU Operation
		bins NOT_ADD = (`NOT => `ADD);
		bins NOT_AND = (`NOT => `AND);
		bins NOT_NOT = (`NOT => `NOT);

		//NOT --> Load Instruction
		bins NOT_LD  = (`NOT => `LD);
		bins NOT_LDR = (`NOT => `LDR);
		bins NOT_LDI = (`NOT => `LDI);
		bins NOT_LEA = (`NOT => `LEA);

		//NOT --> Store Instruction
		bins NOT_ST  = (`NOT => `ST);
		bins NOT_STR = (`NOT => `STR);
		bins NOT_STI = (`NOT => `STI);

		//NOT --> Control Instruction
		bins NOT_BR  = (`NOT => `BR);
		bins NOT_JMP = (`NOT => `JMP);

	}

cov_opcode_LD_others : coverpoint dec.golden_ref.IR[15:12]
	{
		//LD--> ALU Operation
		bins LD_ADD = (`LD => `ADD);
		bins LD_AND = (`LD => `AND);
		bins LD_NOT = (`LD => `NOT);

                //LD --> Control Instruction
		bins LD_BR  = (`LD => `BR);
		bins LD_JMP = (`LD => `JMP);

	}

Cov_opcode_LDR_others : coverpoint dec.golden_ref.IR[15:12] 
	{
		//LDR--> ALU Operation
		bins LDR_ADD = (`LDR => `ADD);
		bins LDR_AND = (`LDR => `AND);
		bins LDR_NOT = (`LDR => `NOT);

		//LDR --> Control Instruction		
		bins LDR_BR  = (`LDR => `BR);
		bins LDR_JMP = (`LDR => `JMP);
	}

Cov_opcode_LDI_others : coverpoint dec.golden_ref.IR[15:12] 
	{
		//LDI--> ALU Operation
		bins LDI_ADD = (`LDI => `ADD);
		bins LDI_AND = (`LDI => `AND);
		bins LDI_NOT = (`LDI => `NOT);

		//LDI --> Control Instruction
		bins LDI_BR  = (`LDI => `BR);
		bins LDI_JMP = (`LDI => `JMP);


	}

Cov_opcode_ST_others : coverpoint dec.golden_ref.IR[15:12] 
	{
		//ST--> ALU Operation
		bins ST_ADD = (`ST => `ADD);
		bins ST_AND = (`ST => `AND);
		bins ST_NOT = (`ST => `NOT);

		//ST --> Control Instruction
		bins ST_BR  = (`ST => `BR);
		bins ST_JMP = (`ST => `JMP);


	}

Cov_opcode_STR_others : coverpoint dec.golden_ref.IR[15:12] 
	{
		//STR--> ALU Operation
		bins STR_ADD = (`STR => `ADD);
		bins STR_AND = (`STR => `AND);
		bins STR_NOT = (`STR => `NOT);

		//STR --> Control Instruction
		bins STR_BR  = (`STR => `BR);
		bins STR_JMP = (`STR => `JMP);

	}

Cov_opcode_STI_others : coverpoint dec.golden_ref.IR[15:12]
	{
		//STI--> ALU Operation
		bins STI_ADD = (`STI => `ADD);
		bins STI_AND = (`STI => `AND);
		bins STI_NOT = (`STI => `NOT);

		//STI--> ALU Operation
		bins STI_BR  = (`STI => `BR);
		bins STI_JMP = (`STI => `JMP);

	}


Cov_opcode_BR_others : coverpoint dec.golden_ref.IR[15:12]
	{
		//BR--> ALU Operation
		bins BR_ADD = (`BR => `ADD);
		bins BR_AND = (`BR => `AND);
		bins BR_NOT = (`BR => `NOT);

		//BR --> Load Instruction
		bins BR_LDR = (`BR => `LDR);
		bins BR_LDI = (`BR => `LDI);
		bins BR_LEA = (`BR => `LEA);

		//BR --> Store Instruction
		bins BR_ST  = (`BR => `ST);
		bins BR_STR = (`BR => `STR);
		bins BR_STI = (`BR => `STI);

	}
Cov_opcode_JMP_others : coverpoint dec.golden_ref.IR[15:12] 
	{
		//JMP--> ALU Operation
		bins JMP_ADD = (`JMP => `ADD);
		bins JMP_AND = (`JMP => `AND);
		bins JMP_NOT = (`JMP => `NOT);

		//JMP --> Load Instruction
		bins JMP_LDR = (`JMP => `LDR);
		bins JMP_LDI = (`JMP => `LDI);
		bins JMP_LEA = (`JMP => `LEA);

		//JMP --> Store Instruction
		bins JMP_ST  = (`JMP => `ST);
		bins JMP_STR = (`JMP => `STR);
		bins JMP_STI = (`JMP => `STI);

	}
endgroup


