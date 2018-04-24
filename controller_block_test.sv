//=================================================================
// ECE 745 ASIC Verification
// Final Project: LC3 Microprocessor Verification
// Class Name: Controller_Block
// Class Author: Harish Anil 
// Inputs: control_block interface
// Outputs: Marked below
// Description: This class monitors the the control bloack of the
// LC3 Microprocessor.  The module being verified is synchronous 
// with the global clock, check for i/p vs. o/p with assertions designed.
//=================================================================
`timescale 10ns / 1ps
`include "macros.sv"

class controller;
int BranchFlag;
virtual controlInterface CtrlInf;
int control_err=0;

function new (virtual controlInterface cif);
	CtrlInf = cif;
endfunction : new

logic [3:0] next_state=0;
typedef struct packed 
{
logic br_taken; 
logic bypass_alu_1;
logic bypass_alu_2;
logic bypass_mem_1;
logic bypass_mem_2;
logic enable_fetch;
logic enable_decode; 
logic enable_execute;
logic enable_writeback;
logic enable_updatePC;
logic [1:0] mem_state;
} golden_ref;
golden_ref cntrl_gref;

task test_control(ref int control_err_count);

@(posedge CtrlInf.clock);
#1;
create_ctrl_gref();
control_debug();
control_err_count=control_err_count + control_err;

if(control_err!=0)
	print_all_lines();
	
control_err=0;

endtask


task print_all_lines();
	$display($time, "==========================Controller Signals===============================");

	$display($time, "    INTERFACE VALUES           -----------------           GOLDENREF           ");
	$display($time, "CtrlInf.enable_updatePC==%b 	----------------- cntrl_gref.enable_updatePC==%b", CtrlInf.enable_updatePC, cntrl_gref.enable_updatePC); 
	$display($time, "CtrlInf.enable_fetch=====%b 	----------------- cntrl_gref.enable_fetch=====%b", CtrlInf.enable_fetch, cntrl_gref.enable_fetch);  
	$display($time, "CtrlInf.enable_decode====%b 	----------------- cntrl_gref.enable_decode====%b", CtrlInf.enable_decode, cntrl_gref.enable_decode);  
	$display($time, "CtrlInf.enable_execute===%b 	----------------- cntrl_gref.enable_execute===%b", CtrlInf.enable_execute, cntrl_gref.enable_execute);  
	$display($time, "CtrlInf.enable_writeback=%b 	----------------- cntrl_gref.enable_writeback=%b", CtrlInf.enable_writeback, cntrl_gref.enable_writeback);  
	$display($time, "CtrlInf.bypass_alu_1=====%b 	----------------- cntrl_gref.bypass_alu_1=====%b", CtrlInf.bypass_alu_1, cntrl_gref.bypass_alu_1);  
	$display($time, "CtrlInf.bypass_alu_2=====%b 	----------------- cntrl_gref.bypass_alu_2=====%b", CtrlInf.bypass_alu_2, cntrl_gref.bypass_alu_2);  
	$display($time, "CtrlInf.bypass_mem_1=====%b 	----------------- cntrl_gref.bypass_mem_1=====%b", CtrlInf.bypass_mem_1, cntrl_gref.bypass_mem_1);  
	$display($time, "CtrlInf.bypass_mem_2=====%b 	----------------- cntrl_gref.bypass_mem_2=====%b", CtrlInf.bypass_mem_2, cntrl_gref.bypass_mem_2);  
	$display($time, "CtrlInf.mem_state========%b 	----------------- cntrl_gref.mem_state========%b", CtrlInf.mem_state, cntrl_gref.mem_state);  
	$display($time, "CtrlInf.br_taken=========%b	----------------- cntrl_gref.br_taken=========%b", CtrlInf.br_taken, cntrl_gref.br_taken);  

	$display($time,"=====================================================================================");
endtask

task create_ctrl_gref();
begin
	

   if(CtrlInf.reset) 
      begin
		cntrl_gref.enable_fetch = 1;
		cntrl_gref.enable_updatePC = 1;
		cntrl_gref.enable_execute = 0;
		cntrl_gref.enable_writeback = 0;
		cntrl_gref.enable_decode = 0;
		cntrl_gref.bypass_alu_1 = 0;
		cntrl_gref.bypass_alu_2 = 0;
		cntrl_gref.bypass_mem_1 = 0;
		cntrl_gref.bypass_mem_2 = 0;
		cntrl_gref.mem_state = 3;
		cntrl_gref.br_taken = 0;	
		next_state = 0;
    end
   else 
     begin
	if(next_state==0)
	 begin
		cntrl_gref.enable_fetch = 1;
		cntrl_gref.enable_updatePC = 1;
		next_state = 1;
	 end
	else if(next_state == 1) 
	begin
		cntrl_gref.enable_execute = 0;
		cntrl_gref.enable_writeback = 0;
		cntrl_gref.mem_state = 3; 
		next_state = 2;
		
		if(((CtrlInf.IMem_dout[15:12]==`BR) || (CtrlInf.IMem_dout[15:12]==`JMP))) //FIX_ME
		 begin
			cntrl_gref.enable_fetch = 0;
			cntrl_gref.enable_updatePC = 0;
			if(cntrl_gref.enable_decode==1)
				next_state = 5;
		 end
		
		cntrl_gref.enable_decode = 1;
	 end
	else if(next_state == 2)
		begin
			cntrl_gref.enable_fetch = 1;
			cntrl_gref.enable_updatePC = 1;
			cntrl_gref.enable_execute = 1;
			cntrl_gref.mem_state = 3;
			cntrl_gref.enable_writeback = 0;
			next_state = 3;
			if(((CtrlInf.IMem_dout[15:12]==`BR) || (CtrlInf.IMem_dout[15:12]==`JMP))) //FIX_ME
			 begin
				cntrl_gref.enable_fetch = 0;
				cntrl_gref.enable_updatePC = 0;
				if(cntrl_gref.enable_decode==1)
				begin
					next_state = 4;
				end
			 end
		end
	else if(next_state==3)
		begin
			cntrl_gref.enable_writeback = 1;
			cntrl_gref.mem_state = 3; 
			next_state = 3;
			
			if((CtrlInf.IR_Exec[15:12]==`LD) || (CtrlInf.IR_Exec[15:12]==`LDR))
			  begin
				cntrl_gref.enable_fetch = 0;
				cntrl_gref.enable_updatePC = 0;
				cntrl_gref.enable_execute = 0;
				cntrl_gref.enable_writeback = 0;
				cntrl_gref.enable_decode = 0;
				cntrl_gref.mem_state = 0;
				next_state = 7;
	   	          end
			else if((CtrlInf.IR_Exec[15:12]==`ST) || (CtrlInf.IR_Exec[15:12]==`STR))
			  begin
				cntrl_gref.enable_fetch = 0;
				cntrl_gref.enable_updatePC = 0;
				cntrl_gref.enable_execute = 0;
				cntrl_gref.enable_writeback = 0;
				cntrl_gref.enable_decode = 0;
				cntrl_gref.mem_state = 2;
				next_state = 8;
			  end
			else if(CtrlInf.IR_Exec[15:12]==`LDI)
		  	  begin
				cntrl_gref.enable_fetch = 0;
				cntrl_gref.enable_updatePC = 0;
				cntrl_gref.enable_execute = 0;
				cntrl_gref.enable_writeback = 0;
				cntrl_gref.enable_decode = 0;
				cntrl_gref.mem_state = 1;
				next_state = 9;
			  end
			else if(CtrlInf.IR_Exec[15:12]==`STI)
			  begin
				cntrl_gref.enable_fetch = 0;
				cntrl_gref.enable_updatePC = 0;
				cntrl_gref.enable_execute = 0;
				cntrl_gref.enable_writeback = 0;
				cntrl_gref.enable_decode = 0;
				cntrl_gref.mem_state = 1;
				next_state = 10;
			  end
			else if((CtrlInf.IMem_dout[15:12]==`BR)||(CtrlInf.IMem_dout[15:12]==`JMP))
			  begin
				cntrl_gref.enable_fetch = 0;
				cntrl_gref.enable_updatePC = 0;
				cntrl_gref.mem_state = 3;
				next_state = 4 ;
			  end
		end
	
	else if(next_state==4)   
		begin
			cntrl_gref.enable_decode = 0;
			cntrl_gref.enable_execute = 1;
			cntrl_gref.enable_writeback = 1;
			next_state = 5;
			if((CtrlInf.IR_Exec[15:12]==`LD) || (CtrlInf.IR_Exec[15:12]==`LDR))
			  begin
				cntrl_gref.enable_fetch = 0;
				cntrl_gref.enable_updatePC = 0;
				cntrl_gref.enable_execute = 0;
				cntrl_gref.enable_writeback = 0;
				cntrl_gref.enable_decode = 0;
				cntrl_gref.mem_state = 0;
				next_state = 7;
	   	          end
			else if((CtrlInf.IR_Exec[15:12]==`ST) || (CtrlInf.IR_Exec[15:12]==`STR))
			  begin
				cntrl_gref.enable_fetch = 0;
				cntrl_gref.enable_updatePC = 0;
				cntrl_gref.enable_execute = 0;
				cntrl_gref.enable_writeback = 0;
				cntrl_gref.enable_decode = 0;
				cntrl_gref.mem_state = 2;
				next_state = 8;
			  end
			else if(CtrlInf.IR_Exec[15:12]==`LDI)
		  	  begin
				cntrl_gref.enable_fetch = 0;
				cntrl_gref.enable_updatePC = 0;
				cntrl_gref.enable_execute = 0;
				cntrl_gref.enable_writeback = 0;
				cntrl_gref.enable_decode = 0;
				cntrl_gref.mem_state = 1;
				next_state = 9;
			  end
			else if(CtrlInf.IR_Exec[15:12]==`STI)
			  begin
				cntrl_gref.enable_fetch = 0;
				cntrl_gref.enable_updatePC = 0;
				cntrl_gref.enable_execute = 0;
				cntrl_gref.enable_writeback = 0;
				cntrl_gref.enable_decode = 0;
				cntrl_gref.mem_state = 1;
				next_state = 10;
			  end
			   
		end
	else if(next_state==5)
		begin
			cntrl_gref.enable_decode = 0;
			cntrl_gref.enable_execute = 0;
			cntrl_gref.enable_writeback = 0;
			next_state = 6;
		end
	else if(next_state==6)
		begin
			cntrl_gref.enable_updatePC= 1;
			cntrl_gref.enable_fetch = 1;
			next_state = 1;		
		end	  
	else if(next_state==7)
		  begin
			cntrl_gref.enable_fetch = 1;
			cntrl_gref.enable_updatePC = 1;
			cntrl_gref.enable_execute = 1;
			cntrl_gref.enable_writeback = 1;
			cntrl_gref.enable_decode = 1;
			cntrl_gref.mem_state = 3;
			next_state = 3;	
			if((CtrlInf.IR[15:12]==`BR)||(CtrlInf.IR[15:12]==`JMP))
			  begin
				cntrl_gref.enable_fetch=0;
				cntrl_gref.enable_updatePC = 0;
				cntrl_gref.enable_decode= 0;
				cntrl_gref.mem_state = 3;
				next_state=5;
			  end
			else if((CtrlInf.IMem_dout[15:12]==`BR)||(CtrlInf.IMem_dout[15:12]==`JMP))
			  begin
				cntrl_gref.enable_fetch = 0;
				cntrl_gref.enable_updatePC = 0;
				cntrl_gref.mem_state = 3;
				next_state = 4 ;
			  end
		  end	  
		  
	else if(next_state==8)
		  begin
			cntrl_gref.enable_fetch = 1;
			cntrl_gref.enable_updatePC = 1;
			cntrl_gref.enable_execute = 1;
			cntrl_gref.enable_writeback = 0;
			cntrl_gref.enable_decode = 1;
			cntrl_gref.mem_state = 3;
			next_state = 3;
			if((CtrlInf.IR[15:12]==`BR)||(CtrlInf.IR[15:12]==`JMP))
			  begin
				cntrl_gref.enable_fetch=0;
				cntrl_gref.enable_updatePC = 0;
				cntrl_gref.enable_decode= 0;
				cntrl_gref.mem_state = 3;
				next_state=5;
			  end
			else if((CtrlInf.IMem_dout[15:12]==`BR)||(CtrlInf.IMem_dout[15:12]==`JMP))
			  begin
				cntrl_gref.enable_fetch = 0;
				cntrl_gref.enable_updatePC = 0;
				cntrl_gref.mem_state = 3;
				next_state = 4 ;
			  end
	          end
	else if(next_state==9)
		begin
			cntrl_gref.mem_state = 0;
			next_state = 7;
		end
	else if(next_state==10)
		begin
			cntrl_gref.mem_state = 2;
			next_state = 8;
		end
	
	// Asyn signals bypass ALU and MEM, and BRTaken.
	
	cntrl_gref.bypass_alu_1 = 0;
	cntrl_gref.bypass_alu_2 = 0;
	cntrl_gref.bypass_mem_1 = 0;
	cntrl_gref.bypass_mem_2 = 0;
					
	if((CtrlInf.IR[15:12]==`AND)||(CtrlInf.IR[15:12]==`ADD)||(CtrlInf.IR[15:12]==`NOT)||(CtrlInf.IR[15:12]==`JMP))  
		begin
	        	if((CtrlInf.IR_Exec[15:12]==`ADD)||(CtrlInf.IR_Exec[15:12]==`AND)||(CtrlInf.IR_Exec[15:12]==`NOT)||(CtrlInf.IR_Exec[15:12]==`LEA))
			  begin
				if(CtrlInf.IR_Exec[11:9]==CtrlInf.IR[8:6])
					cntrl_gref.bypass_alu_1 = 1;
				else 
					cntrl_gref.bypass_alu_1 = 0;
				
				if((CtrlInf.IR_Exec[11:9]==CtrlInf.IR[2:0])
				&&(CtrlInf.IR[5]==0)
				&&((CtrlInf.IR[15:12]==`ADD)
				||(CtrlInf.IR[15:12]==`AND)))
				  begin	
					cntrl_gref.bypass_alu_2 = 1;
				  end
				else 
					cntrl_gref.bypass_alu_2 = 0;
			  end
			 // bypass mem_1 and mem_2 
			else if((CtrlInf.IR_Exec[15:12]==`LD)||(CtrlInf.IR_Exec[15:12]==`LDR)||(CtrlInf.IR_Exec[15:12]==`LDI))
			  begin
				if(CtrlInf.IR_Exec[11:9]==CtrlInf.IR[8:6])
					cntrl_gref.bypass_mem_1 = 1;
				else 
					cntrl_gref.bypass_mem_1 = 0;
				
				if((CtrlInf.IR_Exec[11:9]==CtrlInf.IR[2:0])&&(CtrlInf.IR[5]==0)&&(CtrlInf.IR[15:12]!=`JMP))
					cntrl_gref.bypass_mem_2 = 1;
				else 
					cntrl_gref.bypass_mem_2 = 0;
			  end
		end

	else if(CtrlInf.IR[15:12]==`LDR)
		begin
	        	if((CtrlInf.IR_Exec[15:12]==`ADD)||(CtrlInf.IR_Exec[15:12]==`AND)||(CtrlInf.IR_Exec[15:12]==`NOT)||(CtrlInf.IR_Exec[15:12]==`LEA))
			begin
				if(CtrlInf.IR_Exec[11:9]==CtrlInf.IR[8:6])
					cntrl_gref.bypass_alu_1 = 1;
				else 
					cntrl_gref.bypass_alu_1 = 0;
			end		
			
		end
	
	else if((CtrlInf.IR[15:12]==`ST)||(CtrlInf.IR[15:12]==`STI))
		begin
	        	if((CtrlInf.IR_Exec[15:12]==`ADD)||(CtrlInf.IR_Exec[15:12]==`AND)||(CtrlInf.IR_Exec[15:12]==`NOT)||(CtrlInf.IR_Exec[15:12]==`LEA))
				begin
					if((CtrlInf.IR_Exec[11:9]==CtrlInf.IR[11:9]))
					  begin
						cntrl_gref.bypass_alu_2 = 1;
					  end
					else 
						cntrl_gref.bypass_alu_2 = 0;
				end
		end
		
	else if(CtrlInf.IR[15:12]==`STR)
		begin
	        	if((CtrlInf.IR_Exec[15:12]==`ADD)||(CtrlInf.IR_Exec[15:12]==`AND)||(CtrlInf.IR_Exec[15:12]==`NOT)||(CtrlInf.IR_Exec[15:12]==`LEA))
			begin
				if(CtrlInf.IR_Exec[11:9]==CtrlInf.IR[8:6])
					cntrl_gref.bypass_alu_1 = 1;
				else 
					cntrl_gref.bypass_alu_1 = 0;
				
				if((CtrlInf.IR_Exec[11:9]==CtrlInf.IR[11:9]))
				  begin
					cntrl_gref.bypass_alu_2 = 1;
				  end
				else 
					cntrl_gref.bypass_alu_2 = 0;
			end		
		end
		
	else if((CtrlInf.IR[15:12]==`JMP))
		begin
	        	if((CtrlInf.IR_Exec[15:12]==`ADD)||(CtrlInf.IR_Exec[15:12]==`AND)||(CtrlInf.IR_Exec[15:12]==`NOT)||(CtrlInf.IR_Exec[15:12]==`LEA))
				begin
					if(CtrlInf.IR_Exec[11:9]==CtrlInf.IR[8:6])
						cntrl_gref.bypass_alu_1 = 1;
					else
						cntrl_gref.bypass_alu_1 = 0;
				end
		end
	cntrl_gref.br_taken	= 0;
	cntrl_gref.br_taken = |(CtrlInf.psr & CtrlInf.NZP);
	if(cntrl_gref.br_taken==1)
		cntrl_gref.enable_updatePC = 1;
				
		
	end 

   end 

endtask

function void control_debug();
		  
			if(cntrl_gref.enable_fetch!=CtrlInf.enable_fetch)
			begin
			$display($time, "[TB][CONTROL][enable_fetch]:[Value from DUT: %b][Value from GR: %b]",CtrlInf.enable_fetch, cntrl_gref.enable_fetch); 
			control_err++;
			end
			
			if(cntrl_gref.enable_decode!=CtrlInf.enable_decode)
			 begin	
			$display($time, "[TB][CONTROL][enable_decode]:[Value from DUT: %b][Value from GR: %b]",CtrlInf.enable_decode, cntrl_gref.enable_decode );  
			control_err++;
			end
			  
			if(cntrl_gref.enable_execute != CtrlInf.enable_execute) 
			begin
			$display($time, "[TB][CONTROL][enable_execute]:[Value from DUT: %b][Value from GR: %b]",CtrlInf.enable_execute, cntrl_gref.enable_execute);  
			control_err++;
			end
			
			if(cntrl_gref.enable_writeback != CtrlInf.enable_writeback) 
			begin
			$display($time, "[TB][CONTROL][enable_writeback]:[Value from DUT: %b][Value from GR: %b]",CtrlInf.enable_writeback, cntrl_gref.enable_writeback);  
			control_err++;
			end
			
			if(cntrl_gref.enable_updatePC != CtrlInf.enable_updatePC)
			begin
			$display($time, "[TB][CONTROL][enable_updatePC]:[Value from DUT: %b][Value from GR: %b]",CtrlInf.enable_updatePC, cntrl_gref.enable_updatePC); 
			control_err++;
			end
	
			if(cntrl_gref.bypass_alu_1 != CtrlInf.bypass_alu_1) 
			begin
			$display($time, "[TB][CONTROL][ByPass_ALU_1]:[Value from DUT: %b][Value from GR: %b]", CtrlInf.bypass_alu_1 ,cntrl_gref.bypass_alu_1);  
			control_err++;
			end
			
			if(cntrl_gref.bypass_alu_2 != CtrlInf.bypass_alu_2)
			begin
			$display($time, "[TB][CONTROL][ByPass_ALU_2]:[Value from DUT: %b][Value from GR: %b]", CtrlInf.bypass_alu_2,cntrl_gref.bypass_alu_2);
			control_err++;
			end
			
			if(cntrl_gref.bypass_mem_1 != CtrlInf.bypass_mem_1) 
			begin
			$display($time, "[TB][CONTROL][ByPass_MEM_1]:[Value from DUT: %b][Value from GR: %b]", CtrlInf.bypass_mem_1 ,cntrl_gref.bypass_mem_1);  
			control_err++;
			end
			
			if(cntrl_gref.bypass_mem_2 != CtrlInf.bypass_mem_2) 
			begin
			$display($time, "[TB][CONTROL][ByPass_MEM_2]:[Value from DUT: %b][Value from GR: %b]", CtrlInf.bypass_mem_2 ,cntrl_gref.bypass_mem_2);  
			control_err++;
			end
			
			if(cntrl_gref.mem_state != CtrlInf.mem_state) 
			begin
			$display($time, "[TB][CONTROL][mem_state]:[Value from DUT: %b][Value from GR: %b]", CtrlInf.mem_state,cntrl_gref.mem_state);  	
			control_err++;
			end


			if(cntrl_gref.br_taken != CtrlInf.br_taken) 
			begin
			$display($time, "[TB][CONTROL][BR_TAKEN]:[Value from DUT: %b][Value from GR: %b]", cntrl_gref.br_taken ,CtrlInf.br_taken);  
			control_err++;
			end
		
endfunction //checker

endclass
