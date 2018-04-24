//=================================================================
// ECE 745 ASIC Verification
// Final Project: LC3 Microprocessor Verification
// Class Name: fetch
// Author: Mehrnaz Sadeghian
//=================================================================

class fetch;
int fetch_err=0;

virtual fetchInterface ftif;

	typedef struct packed {
		logic [15:0] npc;
		logic [15:0] pc;
		logic instrmem_rd;
	} fetch_gr; 
	fetch_gr golden_ref;

	
	function new(virtual fetchInterface ft);
		ftif = ft;
	endfunction


	task ft_check(ref int fetch_err_count);
	  set_Values();
	 	golden_ref_chk();
		fetch_err_count=fetch_err_count+fetch_err;
		if(fetch_err>0)
			print_fetch_err();
		fetch_err=0;
	endtask
	
	task set_Values();
		  if(ftif.reset) begin			  
		    golden_ref.pc = 16'h3000;
			golden_ref.npc = 16'h3001;
			golden_ref.instrmem_rd = 1'd1;
		  end
		 else begin
		    if(ftif.enable_fetch) 
			begin
				golden_ref.instrmem_rd = 1'b1;
					if(ftif.enable_updatePC) 
					begin
						@(posedge ftif.clock);
						if(ftif.br_taken) 
							golden_ref.pc = ftif.taddr;
						else 
							golden_ref.pc = golden_ref.npc;
						golden_ref.npc = golden_ref.pc + 1;
					end
			end
			else 
			begin
			  golden_ref.pc=golden_ref.pc;
			  golden_ref.instrmem_rd = 1'b0;
			end
		end
	endtask

	
	function golden_ref_chk();
		if(golden_ref.pc != ftif.pc) begin
			$display($time, "[TB][FETCH][PC]:[Value from DUT: %h][Value from GR: %h]",ftif.pc, golden_ref.pc);
			fetch_err++;
		end
		if(golden_ref.npc != ftif.npc) begin
			$display($time, "[TB][FETCH][NPC]:[Value from DUT: %h][Value from GR: %h]",ftif.npc, golden_ref.npc);
			fetch_err++;
		end
		if(golden_ref.instrmem_rd != ftif.instrmem_rd) begin
			$display($time, "[TB][FETCH][instrmem_rd]:[Value from DUT: %b][Value from GR: %b]",ftif.instrmem_rd, golden_ref.instrmem_rd);
			fetch_err++;
		end
	endfunction

	task print_fetch_err();
		$display("========================================================");
		$display("Fetch Golden Reference: ");
		$display("PC: %h", golden_ref.pc);
		$display("NPC: %h", golden_ref.npc);
		$display("instrmem_rd: %b", golden_ref.npc);
		$display("========================================================");
		$display("DUT Fetch Outputs: ");
		$display("enable_updatePC: %b",ftif.enable_updatePC);
		$display("enable_fetch: %b",ftif.enable_fetch);
		$display("br_taken: %b",ftif.br_taken);
		$display("instrmem_rd: %b",ftif.instrmem_rd);
		$display("taddr: %h", ftif.taddr);
		$display("pc: %h", ftif.pc);
		$display("npc: %h", ftif.npc);
	endtask

endclass





