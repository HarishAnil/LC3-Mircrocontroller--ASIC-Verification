`include "macros.sv"


class Instr_Mem;

	rand bit [3:0] opcode;
	rand bit [2:0] dr;
	rand bit [2:0] sr1;
	rand bit imm_set_bit;
	rand bit [2:0] sr2;
	rand logic [4:0] imm5;
	rand logic [8:0] PCoffset9;
	rand bit [2:0] BaseR;
	rand logic [5:0] PCoffset6;
	rand bit [2:0] NZP;
	//rand bit [2:0] PSR;
	rand bit complete_instr;
	rand bit complete_data;
	rand bit [15:0] Data_dout;
	int control_inst_counter;
	int mem_inst_counter;
	logic  [15:0] IR;
		
	constraint all_instr { opcode inside { `ADD, `AND, `NOT, `LD, `LDR, `LDI, `LEA, `ST, `STR, `STI, `BR, `JMP};};
	constraint ALU_and_Mem{ opcode inside {`ADD, `AND, `NOT,`LDR, `LEA, `LDI, `ST, `STR, `STI};};
	constraint ALU_and_Cntrl { opcode inside {`ADD, `AND, `NOT, `BR, `JMP};};
	constraint ALU_const { opcode inside {`ADD, `AND, `NOT};};
	constraint data_constraints { Data_dout inside { 16'b0101010101010101, 16'b1010101010101010};};

	
	constraint nzp { NZP inside { [1:7]};};
	
	function void Instr_pack(logic instrmem_rd);
	if(instrmem_rd)  begin
		//Increment delay counters for control & memory instructions
		control_inst_counter++;
		mem_inst_counter++;
		//All opcodes valid initially
		this.all_instr.constraint_mode(1);
		this.ALU_and_Cntrl.constraint_mode(0);
		this.ALU_and_Mem.constraint_mode(0);
		this.ALU_const.constraint_mode(0);
		
		//Determine which constrains to turn on/off
		if(control_inst_counter<5 && mem_inst_counter<5) begin
			this.all_instr.constraint_mode(0);
			this.ALU_and_Cntrl.constraint_mode(0);
			this.ALU_and_Mem.constraint_mode(0);
			this.ALU_const.constraint_mode(1);
		end
		if(control_inst_counter<5 && !(mem_inst_counter<5)) begin
			this.all_instr.constraint_mode(0);
			this.ALU_and_Cntrl.constraint_mode(0);
			this.ALU_and_Mem.constraint_mode(1);
			this.ALU_const.constraint_mode(0);
		end
		if(mem_inst_counter<5 && !(control_inst_counter<5)) begin
			this.all_instr.constraint_mode(0);
			this.ALU_and_Cntrl.constraint_mode(1);
			this.ALU_and_Mem.constraint_mode(0);
			this.ALU_const.constraint_mode(0);
		end
		
		//Randomize opcode with constraints and assign IR
		this.randomize();
		IR[15:12] = opcode;
		
		if(opcode == `ADD || opcode == `AND) begin
			IR[11:9] = dr;
			IR[8:6] = sr1;
			if( imm_set_bit == 1)
			begin
				IR[5] = imm_set_bit;
				IR[4:0] = imm5;
			end
			else
			begin
				IR[5:3] = 3'b000;
				IR[2:0] = sr2;
			end
		end
		
		if(opcode == `NOT) begin
			IR[11:9] = dr;
			IR[8:6] = sr1;
			IR[5:0] = 6'b111111;
		end
		
		if(opcode == `LDI || opcode == `LEA || opcode == `LD) begin
			mem_inst_counter=0;
			IR[11:9] = dr;
			IR[8:0] = PCoffset9;
		end
		
		if(opcode == `ST || opcode == `STI) begin
			mem_inst_counter=0;
			IR[11:9] = sr1;
			IR[8:0] = PCoffset9;
		end
		
		if(opcode == `LDR) begin
			mem_inst_counter=0;
			IR[11:9] = dr;
			IR[8:6] = BaseR;
			IR[5:0] = PCoffset6;
		end
		
		if(opcode == `STR) begin
			mem_inst_counter=0;
			IR[11:9] = sr1;
			IR[8:6] = BaseR;
			IR[5:0] = PCoffset6;
		end	
	
		if(opcode == `BR) begin
			control_inst_counter=0;
			IR[11:9] = NZP;
			IR[8:0] = PCoffset9;
		end
		
		if(opcode == `JMP) begin
			control_inst_counter=0;
			IR[11:9] = 3'b000;
			IR[8:6] = BaseR;
			IR[5:0] = 6'b000000;
		end	
		IR_print(IR);
		end

	endfunction
	
	function void IR_print(logic [15:0] IR);
		case(IR[15:12])
	  `ADD: begin
	    if(IR[5])
		 $display($time, "ps [INS_MEM][OPCODE: IMMEDIATE ADD][DR: R%d][SR1: R%d][Imm5 value: %d]",IR[11:9],IR[8:6], IR[4:0]);
		else
		 $display($time, "ps [INS_MEM][OPCODE: ADD][DR: R%d][SR: R%d][SR2: R%d]",IR[11:9],IR[8:6], IR[2:0]);
	  end
	  `AND: begin
	    if(IR[5])
		 $display($time, "ps [INS_MEM][OPCODE: IMMEDIATE AND][DR: R%d][SR1: R%d][Imm5 value: %d]",IR[11:9],IR[8:6], IR[4:0]);
		else
		 $display($time, "ps [INS_MEM][OPCODE: AND][DR: R%d][SR: R%d][SR2: R%d]",IR[11:9],IR[8:6], IR[2:0]);
	  end
	  `NOT: $display($time, "ps [INS_MEM][OPCODE: NOT][DR: R%d][SR1: R%d]",IR[11:9],IR[8:6]);
	  `LD: $display($time, "ps [INS_MEM][OPCODE: LD][DR: R%d][PCOFFSET: %d]",IR[11:9],IR[8:0]);
	  `LDR: $display($time, "ps [INS_MEM][OPCODE: LDR][DR: R%d][BASE_R: R%d][PCOFFSET: %d]",IR[11:9],IR[8:6],IR[5:0]);
	  `LDI: $display($time, "ps [INS_MEM][OPCODE: LDI][DR: R%d][PCOFFSET: %d]",IR[11:9],IR[8:0]);
	  `LEA: $display($time, "ps [INS_MEM][OPCODE: LEA][DR: R%d][PCOFFSET: %d]",IR[11:9],IR[8:0]);
	  `ST: $display($time, "ps [INS_MEM][OPCODE: ST][SR: R%d][PCOFFSET: %d]",IR[11:9],IR[8:0]);
	  `STR: $display($time, "ps [INS_MEM][OPCODE: STR][SR: R%d][BASE_R: R%d][PCOFFSET: %d]",IR[11:9], IR[8:6],IR[5:0]);
	  `STI: $display($time, "ps [INS_MEM][OPCODE: STI][SR: R%d][PCOFFSET: %d]",IR[11:9],IR[8:0]);
	  `BR: $display($time, "ps [INS_MEM][OPCODE: BR][NZP: %b][PCOFFSET: %d]",IR[11:9],IR[8:0]);
	  `JMP: $display($time, "ps [INS_MEM][OPCODE: JMP][BASE_R: R%d]",IR[8:6]);
	  default: $display($time, "ps [INS_MEM]ERROR: invalid opcode generated: %b", IR[15:12]);
	  endcase
	endfunction
	
	function void initialize_rf(int i);
	IR[15:12]=4'b0101;
	IR[11:9]=i;
	IR[8:6]=i;
	IR[5]=1'b1;
	IR[4:0]=5'd0;
	endfunction
	
	endclass
