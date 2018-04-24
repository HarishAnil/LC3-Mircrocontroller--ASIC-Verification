`include "macros.sv"
class execute;

	//outputs
	typedef struct{
	logic [15:0] aluout, pcout;
	logic [1:0]  W_Control_out;
	logic	Mem_Control_out;
	logic [15:0] M_Data;
	logic [2:0]  dr;
	logic [2:0]  sr1, sr2;  
	logic [2:0]  NZP;
	logic [15:0] IR_Exec;
	logic [15:0] aluin1_out, aluin2_out;
	} golden_ref;
	golden_ref exe_gr_out;
	int execute_err=0;
	logic [15:0] Aluin1, Aluin2;

	//virtual interface declaration
	virtual executeInterface exe_intf;
	
	
	function new(virtual executeInterface exIf);
		exe_intf=exIf;
	endfunction
	
	task execute_check(ref int execute_err_count);
		check_exe();
		if(execute_err>0)
			print_exe_err();
		execute_err_count=execute_err_count+execute_err;
		execute_err=0;
		exe_gr();

		async_gr();
		check_async();
		execute_err_count=execute_err_count+execute_err;
		if(execute_err>0)
			print_exe_err();
		execute_err=0;
	endtask
	
	
	task exe_gr();
		if(exe_intf.reset)
		begin
			exe_gr_out.aluout = 16'b0;
			exe_gr_out.pcout = 16'b0;
			exe_gr_out.W_Control_out = 2'b0;
			exe_gr_out.Mem_Control_out = 0;
			exe_gr_out.NZP = 3'b0;
			exe_gr_out.IR_Exec = 16'b0;
			exe_gr_out.dr = 3'b0;
			exe_gr_out.M_Data = 16'b0;
			exe_gr_out.sr1 = 0;
			exe_gr_out.sr2 = 0;
		end	
		else
		begin
			if(exe_intf.enable_execute == 0)
			begin
				exe_gr_out.NZP = 3'b0;
			end
			else if(exe_intf.enable_execute == 1)
			    begin
					exe_gr_out.W_Control_out = exe_intf.W_Control_in;
					exe_gr_out.Mem_Control_out = exe_intf.Mem_Control_in;
					exe_gr_out.IR_Exec = exe_intf.IR;
					
					Aluin1 = bypass_fir(exe_intf.bypass_alu_1, exe_intf.bypass_mem_1, exe_intf.VSR1, exe_intf.Mem_Bypass_Val, exe_gr_out.aluout);
					Aluin2 = bypass_sec(exe_intf.bypass_alu_2, exe_intf.bypass_mem_2, exe_intf.IR[5], exe_intf.IR[4:0], exe_intf.VSR2, exe_intf.Mem_Bypass_Val, exe_gr_out.aluout);
					
					exe_gr_out.M_Data = exe_intf.VSR2;
					if(exe_intf.bypass_alu_2) 
						exe_gr_out.M_Data = Aluin2;
					
					if((exe_intf.IR[15:12]== `ADD)||(exe_intf.IR[15:12]==`AND)||(exe_intf.IR[15:12]==`NOT)||(exe_intf.IR[15:12]==`LD)||(exe_intf.IR[15:12]==`LDR)||(exe_intf.IR[15:12]==`LDI)||(exe_intf.IR[15:12]==`LEA))
			       		exe_gr_out.dr  <= exe_intf.IR[11:9];
					else 
			       		exe_gr_out.dr = 3'b0;

					if(exe_intf.IR[15:12] == `BR)
			          exe_gr_out.NZP = exe_intf.IR[11:9];
					else if(exe_intf.IR[15:12] == `JMP)
			          exe_gr_out.NZP = 3'b111;
					else
			          exe_gr_out.NZP = 3'b0;
					  
					if(exe_intf.IR[15:12] == `ADD || exe_intf.IR[15:12] == `AND || exe_intf.IR[15:12] == `NOT)
					begin
						if(exe_intf.E_Control[5:4] == 2'b00)
			       			exe_gr_out.aluout = Aluin1 + Aluin2;
			       		else if(exe_intf.E_Control[5:4] == 2'b01)
			       			exe_gr_out.aluout = Aluin1 & Aluin2;
			       		else if(exe_intf.E_Control[5:4] == 2'b10)
			       			exe_gr_out.aluout = ~(Aluin1);
			       		else
			       			exe_gr_out.aluout = 16'b0;

			       		exe_gr_out.pcout = exe_gr_out.aluout;
					end
					else
					begin
						if(exe_intf.E_Control[3:2]==2'b00)					//Offset 11
				          begin
				                 if(exe_intf.E_Control[1])
				                 exe_gr_out.pcout = exe_intf.npc_in - 16'b1 + {{5{exe_intf.IR[10]}},exe_intf.IR[10:0]}; 		
				                 else
				                 exe_gr_out.pcout = Aluin1 + {{5{exe_intf.IR[10]}},exe_intf.IR[10:0]};
				              end
						else if(exe_intf.E_Control[3:2]==2'b01)						//Offset  9
				          begin
				                 if(exe_intf.E_Control[1])
				                 exe_gr_out.pcout = exe_intf.npc_in - 16'b1 + {{7{exe_intf.IR[8]}},exe_intf.IR[8:0]};
				                 else
				                 exe_gr_out.pcout = Aluin1 + {{7{exe_intf.IR[8]}},exe_intf.IR[8:0]};
				              end
						else if(exe_intf.E_Control[3:2]==2'b10)				//Offset 6
				          begin
				                 if(exe_intf.E_Control[1])
				                 exe_gr_out.pcout = exe_intf.npc_in - 16'b1 + {{10{exe_intf.IR[5]}},exe_intf.IR[5:0]};
				                 else
				                 exe_gr_out.pcout = Aluin1 + {{10{exe_intf.IR[5]}},exe_intf.IR[5:0]};
				              end
						else if(exe_intf.E_Control[3:2]==2'b11)				//Offset of 0
				          begin
				                 if(exe_intf.E_Control[1])
								 exe_gr_out.pcout = exe_intf.npc_in - 16'b1;
				                 else
				                 exe_gr_out.pcout = Aluin1;
				              end
						else 
				          exe_gr_out.pcout = 16'b0;
						
						exe_gr_out.aluout = exe_gr_out.pcout;
					end
				end
				
		end
			
	endtask
	
	task async_gr();
				if(!exe_intf.reset)
				begin
					case(exe_intf.IR[8:6])
						3'b111: exe_gr_out.sr1 = exe_intf.IR[8:6];
						3'b110: exe_gr_out.sr1 = exe_intf.IR[8:6];
						3'b101: exe_gr_out.sr1 = exe_intf.IR[8:6];
						3'b100: exe_gr_out.sr1 = exe_intf.IR[8:6];
						3'b011: exe_gr_out.sr1 = exe_intf.IR[8:6];
						3'b010: exe_gr_out.sr1 = exe_intf.IR[8:6];
						3'b001: exe_gr_out.sr1 = exe_intf.IR[8:6];
						default: exe_gr_out.sr1 = 0;
					endcase
						
					case(exe_intf.IR[15:12])
						`ADD: exe_gr_out.sr2 = exe_intf.IR[2:0]; 
						`AND: exe_gr_out.sr2 = exe_intf.IR[2:0];
						`NOT: exe_gr_out.sr2 = exe_intf.IR[2:0];
						`ST: exe_gr_out.sr2 = exe_intf.IR[11:9];
						`STR: exe_gr_out.sr2 = exe_intf.IR[11:9];
						`STI: exe_gr_out.sr2 = exe_intf.IR[11:9];
						default: exe_gr_out.sr2 = 3'b0;
					endcase
				end
	endtask
	function check_exe();
	        if(exe_gr_out.aluout != exe_intf.aluout)begin
	            $display($time,"[TB] [EXECUTE] BUG IN EXE STAGE DUT aluout_DUT = %h | aluout = %h\n",exe_intf.aluout,exe_gr_out.aluout);

				execute_err++;
			end

	        if(exe_gr_out.pcout != exe_intf.pcout)begin
	            $display($time,"[TB] [EXECUTE] BUG IN EXECUTE DUT pcout_DUT = %h | pcout = %h\n",exe_intf.pcout,exe_gr_out.pcout);

				execute_err++;
			end

	        if(exe_gr_out.NZP != exe_intf.NZP)begin
	            $display($time,"[TB] [EXECUTE] BUG IN EXECUTE DUT NZP_DUT = %b | NZP = %b\n",exe_intf.NZP,exe_gr_out.NZP);

				execute_err++;
			end

	        if(exe_gr_out.dr != exe_intf.dr)begin
	            $display($time,"[TB] [EXECUTE] BUG IN EXECUTE DUT dr_DUT = %b | dr = %b\n",exe_intf.dr,exe_gr_out.dr);

				execute_err++;
			end
	        if(exe_gr_out.M_Data != exe_intf.M_Data)begin
	            $display($time,"[TB] [EXECUTE] BUG IN EXECUTE DUT M_Data_DUT = %h | M_Data = %h | exe_intf.VSR2 = %h | exe_intf.bypass_alu_2 = %b\n",exe_intf.M_Data,exe_gr_out.M_Data, exe_intf.VSR2, exe_intf.bypass_alu_2);

				execute_err++;
			end
	        
			if(exe_gr_out.W_Control_out != exe_intf.W_Control_out)begin
					$display($time,"[TB] [EXECUTE] BUG IN EXECUTE DUT W_Control_out_DUT = %h | W_Control_out = %h\n",exe_intf.W_Control_out,exe_gr_out.W_Control_out);

					execute_err++;
			end
				
			if(exe_gr_out.Mem_Control_out != exe_intf.Mem_Control_out)begin
					$display($time,"[TB] [EXECUTE] BUG IN EXECUTE DUT Mem_Control_out_DUT = %h | Mem_Control_out = %h\n",exe_intf.Mem_Control_out,exe_gr_out.Mem_Control_out);

					execute_err++;
			end
			
				
			if(exe_gr_out.IR_Exec != exe_intf.IR_Exec)begin
					$display($time,"[TB] [EXECUTE] BUG IN EXECUTE DUT IR_Exec_DUT = %h | IR_Exec = %h\n",exe_intf.IR_Exec,exe_gr_out.IR_Exec);
					
					execute_err++;
			end

	endfunction
	
	function int check_async();
	        if(exe_gr_out.sr1 != exe_intf.sr1) begin
				$display("IR[8:6]:",exe_intf.IR[8:6]);
	            $display($time,"[TB] [EXECUTE] BUG IN EXECUTE DUT sr1_DUT = %b | sr1 = %b | IR[8:6] = %b \n",exe_intf.sr1,exe_gr_out.sr1,exe_intf.IR[8:6]);
				
				execute_err++;
			end
	        if(exe_gr_out.sr2 != exe_intf.sr2) begin
	            $display($time,"[TB] [EXECUTE] BUG IN EXECUTE DUT sr2_DUT = %b | sr2 = %b\n",exe_intf.sr2,exe_gr_out.sr2,);
				
				execute_err++;
			end
	endfunction
	
function logic [15:0] bypass_sec(logic bypass_alu_2, logic bypass_mem_2, logic mode, logic [4:0] imm5, logic [15:0] VSR2, logic [15:0] Mem_Bypass_Val, logic [15:0] aluout);
   case({bypass_mem_2,bypass_alu_2})
      2'b01: return aluout;
      2'b10: return Mem_Bypass_Val;
      default: begin
                  if(mode == 0)
                     return VSR2;
                  else
                     return {{11{imm5[4]}},imm5[4:0]};					//sign extension of imm5[4]
               end
   endcase
endfunction
	
function logic [15:0] bypass_fir(logic bypass_alu_1, logic bypass_mem_1, logic [15:0] VSR1, logic [15:0] Mem_Bypass_Val, logic [15:0] aluout);
   case({bypass_mem_1,bypass_alu_1})
      2'b01: return aluout;
      2'b10: return Mem_Bypass_Val;
      default: return VSR1;
   endcase
endfunction	

function print_exe_err();
			$display($time,"========EXECUTE ERROR=========");
			$display($time,"==========Inputs==============");
			$display($time,"  enable_execute = %h",exe_intf.enable_execute);
			$display($time,"  W_Control_in = %h",exe_intf.W_Control_in);
			$display($time,"  Mem_Control_in = %h",exe_intf.Mem_Control_in);
			$display($time,"  E_Control = %b",exe_intf.E_Control);
			$display($time,"  IR = %h",exe_intf.IR);
			$display($time,"  npc = %h",exe_intf.npc_in);
			$display($time,"  VSR1 = %h",exe_intf.VSR1);
			$display($time,"  VSR2 = %h",exe_intf.VSR2);
			$display($time,"  Mem_Bypass_Val = %h",exe_intf.Mem_Bypass_Val);
			$display($time,"  bypass_alu_1 = %h",exe_intf.bypass_alu_1);
			$display($time,"  bypass_alu_2 = %h",exe_intf.bypass_alu_2);
			$display($time,"  bypass_mem_1 = %h",exe_intf.bypass_mem_1);
			$display($time,"  bypass_mem_2 = %h",exe_intf.bypass_mem_2);
			$display($time,"==========DUT Outputs===========");
			$display($time,"  aluout = %h",exe_intf.aluout);
			$display($time,"  pcout = %h",exe_intf.pcout);
			$display($time,"  W_Control_out = %h",exe_intf.W_Control_out);
			$display($time,"  Mem_Control_out = %h",exe_intf.Mem_Control_out);
			$display($time,"  NZP = %b",exe_intf.NZP);
			$display($time,"  IR_Exec = %b",exe_intf.IR_Exec);
			$display($time,"  sr1 = %b",exe_intf.sr1);
			$display($time,"  sr2 = %b",exe_intf.sr2);
			$display($time,"  dr = %b",exe_intf.dr);
			$display($time,"  M_Data = %h",exe_intf.M_Data);
			$display($time,"===========GR OUTPUT===========");
			$display($time,"  aluout = %h",exe_gr_out.aluout);
			$display($time,"  pcout = %h",exe_gr_out.pcout);
			$display($time,"  W_Control_out = %h",exe_gr_out.W_Control_out);
			$display($time,"  Mem_Control_out = %h",exe_gr_out.Mem_Control_out);
			$display($time,"  NZP = %b",exe_gr_out.NZP);
			$display($time,"  IR_Exec = %b",exe_gr_out.IR_Exec);
			$display($time,"  sr1 = %b",exe_gr_out.sr1);
			$display($time,"  sr2 = %b",exe_gr_out.sr2);
			$display($time,"  dr = %b",exe_gr_out.dr);
			$display($time,"  M_Data = %h",exe_gr_out.M_Data);
			$display($time,"================================");
endfunction

endclass
