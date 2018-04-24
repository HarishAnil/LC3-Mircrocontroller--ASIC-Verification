//=================================================================
// ECE 745 ASIC Verification
// Final Project: LC3 Microprocessor Verification
// Class Name: mem_access
// Class Author: Ryan Geary
// Inputs: mem_access interface
// Outputs: N/A
// Description: This class monitors the the memory access stage of the
// LC3 Microprocessor.  The module being verified is asynchronous 
// with the global clock, so each time the state of this module 
// changes, all outputs associated with that state are verified
// accordingly.
//=================================================================
 `timescale 10 ns / 1 ps
class mem_access;
virtual memaccessInterface maif;

typedef struct packed {
  logic [15:0] DMem_addr;
  logic [15:0] DMem_din;
  logic DMem_rd;
  logic [15:0] memout;
} mem_access_gr;
mem_access_gr golden_ref;
int mem_acc_err=0;

function new(virtual memaccessInterface ma);
  maif=ma;
endfunction

task ma_check(ref int mem_access_err_count);
	golden_ref_update();
	golden_ref_chk();
	mem_access_err_count=mem_access_err_count+mem_acc_err;
	if(mem_acc_err>0)
		print_ma_err();
	mem_acc_err=0;	
endtask

task print_ma_err();
$display("========================================================");
$display("Mem_Access Golden Reference:");
$display("DMem_addr: %h", golden_ref.DMem_addr);
$display("DMem_din: %h", golden_ref.DMem_din);
$display("DMem_rd: %b", golden_ref.DMem_rd);
$display("memout: %h", golden_ref.memout);
$display("");
$display("DUT Mem Access Outputs:");
$display("mem_state: %h", maif.mem_state);
$display("M_Control: %h", maif.M_Control);
$display("DMem_rd: %h", maif.DMem_rd);
$display("DMem_din: %h", maif.DMem_din);
$display("M_Addr: %h", maif.M_Addr);
$display("DMem_dout: %h", maif.DMem_dout);
$display("DMem_addr: %h", maif.DMem_addr);
$display("memout: %h", maif.memout);
$display("M_Data: %h", maif.M_Data);
$display("========================================================");
endtask

function golden_ref_update();
//Data_rd = 1 for mem_state 0,1
//Data_rd=0 for state 2
//Data_rd=z for state 3
  golden_ref.memout = maif.DMem_dout;
  case(maif.mem_state)
    2'd0: begin
	  golden_ref.DMem_rd = 1'b1;
	  golden_ref.DMem_din = 16'b0;
	  if(maif.M_Control)
	    golden_ref.DMem_addr = maif.DMem_dout;
	  else
	    golden_ref.DMem_addr = maif.M_Addr;
	end
	2'd1: begin
	  golden_ref.DMem_rd = 1'b1;
	  golden_ref.DMem_din = 16'b0;
	  golden_ref.DMem_addr = maif.M_Addr;
	end
    2'd2: begin
	  golden_ref.DMem_rd = 1'b0;
	  golden_ref.DMem_din = maif.M_Data;
	  if(maif.M_Control)
	    golden_ref.DMem_addr = maif.DMem_dout;
	  else
	    golden_ref.DMem_addr = maif.M_Addr;
	end
    2'd3: begin
	  golden_ref.DMem_rd = 1'bz;
	  golden_ref.DMem_din = 16'hzzzz;
	  golden_ref.DMem_addr = 16'hzzzz;
	end
	default: begin
	  golden_ref.DMem_rd = 1'bx;
	  golden_ref.DMem_din = 16'hxxxx;
	  golden_ref.DMem_addr = 16'hxxxx;
	  $display($time, "[TB][MA][mem_state]:[Value from DUT: %d][Value from GR: 0-3]", maif.mem_state);
	end
	endcase
endfunction

function golden_ref_chk();
  if(golden_ref.DMem_rd != maif.DMem_rd) begin
    $display($time, "[TB][MA][DMem_rd]:[Value from DUT: %b][Value from GR: %b]", maif.DMem_rd, golden_ref.DMem_rd);
    mem_acc_err++;
  end
  if(golden_ref.DMem_din != maif.DMem_din) begin
    $display($time, "[TB][MA][DMem_in]:[Value from DUT: %h][Value from GR: %h]", maif.DMem_din, golden_ref.DMem_din);
    mem_acc_err++;
  end
  if(golden_ref.DMem_addr != maif.DMem_addr) begin
    $display($time, "[TB][MA][DMem_addr]:[Value from DUT: %h][Value from GR: %h]", maif.DMem_addr, golden_ref.DMem_addr);
    mem_acc_err++;
  end
  if(golden_ref.memout != maif.memout) begin
    $display($time, "[TB][MA][memout]:[Value from DUT: %h][Value from GR: %h]", maif.memout, golden_ref.memout);
	mem_acc_err++;
  end
endfunction
endclass
