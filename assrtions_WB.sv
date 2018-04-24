		
		//---------------Asserting all bypass signals for all combination----------------// 
		// Refer the controls test block if the IR_Ex and IR Dest and Source match flag the bypass accordingly.
		// Not all combination in testbench covered here, only those mentioned in coverage plan.
		// No Control signals asserted here
		
		property CTRL_bypass_alu_1_AA; // ALU after ALU instruction (Removed LEA)
			@(posedge clock)
		((IR[15:12] == 'ADD) || (IR[15:12] == 'AND) || (IR[15:12] == 'NOT)) && ((IR_Exec[15:12] == 'ADD) || (IR_Exec[15:12] == 'AND) || (IR_Exec[15:12] == 'NOT) /*|| (IR_Exec[15:12] == 'LEA)*/) && (IR_Exec[11:9] == IR[8:6]) |-> bypass_alu_1 == 1'b1;
		endproperty
		assert property (CTRL_bypass_alu_1_AA); 
		cover property  (CTRL_bypass_alu_1_AA);

		property CTRL_bypass_alu_2_AA; // ALU after ALU (Removed LEA)
			@(posedge clock)
		((IR[15:12] == 'ADD) || (IR[15:12] == 'AND) || (IR[15:12] == 'NOT)) 
		&& ((IR_Exec[15:12] == 'ADD) || (IR_Exec[15:12] == 'AND) || (IR_Exec[15:12] == 'NOT)/*|| (IR_Exec[15:12] == 'LEA)*/) 
		&& ((IR_Exec[11:9] == IR[2:0]) && (IR[5] == 1'b0)) |-> bypass_alu_2 == 1'b1;
		endproperty
		assert property (CTRL_bypass_alu_2_AA); 
		cover property  (CTRL_bypass_alu_2_AA);
		
				
		property CTRL_bypass_alu_1_AS; // ALU and store (I have added STR, ST, STI)
			@(posedge clock)
		((IR_Exec[15:12] == 'ADD) || (IR_Exec[15:12] == 'AND) || (IR_Exec[15:12] == 'NOT)) 
		  && ((IR[15:12] == 'STR)||(IR[15:12] == 'ST)||(IR[15:12] == 'STI)) 
		  && (IR_Exec[11:9] == IR[11:9]) |-> bypass_alu_2 == 1'b1;
		endproperty
		assert property (CTRL_bypass_alu_1_AS); 
		cover property  (CTRL_bypass_alu_1_AS);
		
		// property CTRL_bypass_alu_1_AL;  //(this should be der)
		// @(posedge clock)
		// ((IR_Exec[15:12] == 'ADD) || (IR_Exec[15:12] == 'AND) || (IR_Exec[15:12] == NOT)) && (IR[15:12] == LDR) && (IR_Exec[11:9] == IR[8:6]) |-> bypass_alu_1 == 1'b1;
		// endproperty
		// assert property (CTRL_bypass_alu_1_AL); 
		// cover property  (CTRL_bypass_alu_1_AL);
		
		property CTRL_bypass_alu_2_AS; // ALU and store (have excluded LEA) (Base register is a source)
			@(posedge clock)
		((IR_Exec[15:12] == 'ADD) || (IR_Exec[15:12] == 'AND) || (IR_Exec[15:12] == 'NOT) || (IR_Exec[15:12] == 'LEA)) 
			&& (IR[15:12] == 'STR) 
		 && (IR_Exec[11:9] == IR[11:9]) |-> bypass_alu_2 == 1'b1;
		endproperty
		assert property (CTRL_bypass_alu_2_AS); 
		cover property  (CTRL_bypass_alu_2_AS);

		
		//----------------------------bypass_mem line assertions--------------------.
		
		property CTRL_bypass_mem_1_LA;
			@(posedge clock)
		((IR_Exec[15:12] == LD) || (IR_Exec[15:12] == 'LDR) || (IR_Exec[15:12] == 'LDI)) && ((IR[15:12] == 'ADD) || (IR[15:12] == 'AND) || (IR[15:12] == 'NOT)) && (IR_Exec[11:9] == IR[8:6]) |-> bypass_mem_1 == 1'b1;
		endproperty
		assert property (CTRL_bypass_mem_1_LA); 
		cover property  (CTRL_bypass_mem_1_LA);

		property CTRL_bypass_mem_2_LA;
			@(posedge clock)
		((IR_Exec[15:12] == LD) || (IR_Exec[15:12] == 'LDR) || (IR_Exec[15:12] == 'LDI)) && ((IR[15:12] == 'ADD) || (IR[15:12] == 'AND) || (IR[15:12] == 'NOT)) && ((IR_Exec[11:9] == IR[2:0]) && (IR[5] == 1'b0)) |-> bypass_mem_2 == 1'b1;
		endproperty
		assert property (CTRL_bypass_mem_2_LA); 
		cover property  (CTRL_bypass_mem_2_LA);
		
		property CTRL_bypass_mem_1_LS;
		@(posedge clock)
		((IR_Exec[15:12] == LD) || (IR_Exec[15:12] == 'LDR) || (IR_Exec[15:12] == 'LDI)) && ((IR[15:12] == 'STR) || (IR[15:12] == 'ST) || (IR[15:12] == 'STI))  && (IR_Exec[11:9] == IR[11:9])|-> bypass_mem_2 == 1'b1;
		endproperty
		assert property (CTRL_bypass_mem_1_LS); 
		cover property  (CTRL_bypass_mem_1_LS);
				
		
		property CTRL_bypass_mem_2_LS;
			@(posedge clock)
		((IR_Exec[15:12] == LD) || (IR_Exec[15:12] == 'LDR) || (IR_Exec[15:12] == 'LDI)) && (IR[15:12] == 'STR) && (IR_Exec[11:9] == IR[8:6])|-> bypass_mem_2 == 1'b1;
		endproperty
		assert property (CTRL_bypass_mem_2_LS); 
		cover property  (CTRL_bypass_mem_2_LS);
		
		
		//-------------- mem state changes assertions, refer the spec sheet FSM table, control block is more confusing ------//
		
		
		property CTRL_mem_state_LDI;
			@(posedge clock)
			(IR[15:12] == 'LDI) |=>  mem_state == 2'b01 ##1 mem_state == 2'b00 ##1 mem_state == 2'b11;
		endproperty
		assert property (CTRL_mem_state_LDI); 
		cover property  (CTRL_mem_state_LDI);

		property CTRL_mem_state_STI;
			@(posedge clock)
			(IR[15:12] == 'STI) |=>  mem_state == 2'b01 ##1 mem_state == 2'b10 ##1 mem_state == 2'b11;
		endproperty
		assert property (CTRL_mem_state_STI); 
		cover property  (CTRL_mem_state_STI);

		// property CTRL_enable_mem_state_STI_LDI;
			// @(posedge clock)
			// (IR[15:12] == 'LDI || IR[15:12] == 'STI ) |=>  mem_state == 2'b01 ##2 mem_state == 2'b11;
		// endproperty
		// assert property (CTRL_enable_mem_state_STI_LDI); 
		// cover property  (CTRL_enable_mem_state_STI_LDI);
	
		// property CTRL_enable_mem_state_ST_STR;
			// @(posedge clock)
			// (IR[15:12] == 'ST || IR[15:12] == 'STR ) |=>  mem_state == 2'b10 ##1 mem_state == 2'b11;
		// endproperty
		// assert property (CTRL_enable_mem_state_ST_STR); 
		// cover property  (CTRL_enable_mem_state_ST_STR);
		// property CTRL_enable_mem_state_LD_LDR;
			// @(posedge clock)
			// (IR[15:12] == LD || IR[15:12] == 'LDR ) |=>  mem_state == 2'b00 ##1 mem_state == 2'b11;
		// endproperty
		// assert property (CTRL_enable_mem_state_LD_LDR); 
		// cover property  (CTRL_enable_mem_state_LD_LDR);
		
		//----------------------Wriback block enable-----------------------//

		property CTRL_enable_wb_ST;
			@(posedge clock)
			(Instr_dout[15:12] == 'STR || Instr_dout[15:12] == 'ST) |=> ##2 !enable_writeback ##2 enable_writeback;
		endproperty
		assert property (CTRL_enable_wb_ST);
		cover property  (CTRL_enable_wb_ST);


		property CTRL_mem_state_3_1;
			@(posedge clock)
			(mem_state == 2'b11) && ((IR[15:12] == 'LDI) || (IR[15:12] == 'LDI)) |=>  mem_state == 2'b01;
		endproperty
		assert property (CTRL_mem_state_3_1); 
		cover property  (CTRL_mem_state_3_1);

		property CTRL_mem_state_3_0;
			@(posedge clock)
			(mem_state == 2'b11) && (IR[15:12] == 'LDI) |=>  mem_state == 2'b01 ##1 mem_state == 2'b00;
		endproperty
		assert property (CTRL_mem_state_3_0); 
		cover property  (CTRL_mem_state_3_0);

		property CTRL_mem_state_3_2;
			@(posedge clock)
			(mem_state == 2'b11) && (IR[15:12] == 'STI) |=>  mem_state == 2'b01 ##1 mem_state == 2'b10;
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
			(mem_state == 2'b01) && (IR_Exec[15:12] == 'STI) |=>  mem_state == 2'b10;
		endproperty
		assert property (CTRL_mem_state_1_2); 
		cover property  (CTRL_mem_state_1_2);

		property CTRL_mem_state_1_0;
			@(posedge clock)
			(mem_state == 2'b01) && (IR_Exec[15:12] == 'LDI) |=>  mem_state == 2'b00;
		endproperty
		assert property (CTRL_mem_state_1_0); 
		cover property  (CTRL_mem_state_1_0);

		property CTRL_enable_writeback_fall1;
			@(posedge clock)
			(IR[15:12] == 'ST || IR[15:12] == 'STR || IR[15:12] == LD || IR[15:12] == 'LDR || IR[15:12] == 'LDI || IR[15:12] == 'STI ) |=>  !enable_writeback;
		
		endproperty
		property CTRL_enable_writeback_fall2;
			@(posedge clock)
			(Instr_dout[15:12] == 4'b0000 || Instr_dout[15:12] == 4'b1100) |=>  ##2 !enable_writeback;
		
		endproperty
		
		cover property (CTRL_enable_writeback_fall1);
		cover property (CTRL_enable_writeback_fall2);
		
		property CTRL_enable_writeback_rise1;
			@(posedge clock)
			(IR[15:12] == LD || IR[15:12] == 'LDR ) |=>  ##1 enable_writeback;
		endproperty
		property CTRL_enable_writeback_rise2;
			@(posedge clock)
			(IR[15:12] == 'ST || IR[15:12] == 'STR || IR[15:12] == 'LDI) |=>  ##2 enable_writeback;
		endproperty
		
		property CTRL_enable_writeback_rise3;
			@(posedge clock)
			(IR[15:12] == 'STI) |=>  ##3 enable_writeback;
		endproperty
		property CTRL_enable_writeback_rise4;
			@(posedge clock)
			(Instr_dout[15:12] == 4'b0000) || (Instr_dout[15:12] == 4'b1100) |=>  ##6 enable_writeback;
		endproperty
		
		assert property (CTRL_enable_writeback_rise1); 
		cover property  (CTRL_enable_writeback_rise1);
		assert property (CTRL_enable_writeback_rise2); 
		cover property  (CTRL_enable_writeback_rise2);
		assert property (CTRL_enable_writeback_rise3); 
		cover property  (CTRL_enable_writeback_rise3);
		assert property (CTRL_enable_writeback_rise4); 
		cover property  (CTRL_enable_writeback_rise4);


