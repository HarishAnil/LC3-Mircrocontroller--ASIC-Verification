//=================================================================
// ECE 745 ASIC Verification
// Final Project: LC3 Microprocessor Verification
// Class Name: writeback
// Class Author: Ryan Geary
// Inputs: writeback interface
// Outputs: N/A
// Description: This class monitors the the writeback stage of the
// LC3 Microprocessor.  With each operation, the contents of the
// register file are verified with a reference model and coverage
// statistics are updated and sent to the master scoreboard.
//=================================================================
 `timescale 10 ns / 1 ps
class writeback;
typedef struct {
  logic [15:0] reg_file [7:0];
  logic [2:0] psr;
	logic [15:0] VSR1, VSR2;
} wb_gr;
wb_gr golden_ref;
int wb_err=0;
virtual writebackInterface wbif;

function new(virtual writebackInterface wb);
  wbif=wb;
	golden_ref.reg_file[0]=16'd0;
	golden_ref.reg_file[1]=16'd0;
	golden_ref.reg_file[2]=16'd0;
	golden_ref.reg_file[3]=16'd0;
	golden_ref.reg_file[4]=16'd0;
	golden_ref.reg_file[5]=16'd0;
	golden_ref.reg_file[6]=16'd0;
	golden_ref.reg_file[7]=16'd0;
endfunction

task wb_check(ref int writeback_err_count);
  wb_err=wb_err+rf_golden_ref_update();
  wb_err=wb_err+psr_golden_ref_update();
  #1;
  //fork
		rf_golden_ref_chk();
		psr_chk();
  //join
  writeback_err_count=writeback_err_count+wb_err;
	if(wb_err>0)
		print_wb_err();
	wb_err=0;
endtask

task print_wb_err();
$display("========================================================");
$display("Writeback Golden Reference:");
$display("RF[0]: %h", golden_ref.reg_file[0]);
$display("RF[1]: %h", golden_ref.reg_file[1]);
$display("RF[2]: %h", golden_ref.reg_file[2]);
$display("RF[3]: %h", golden_ref.reg_file[3]);
$display("RF[4]: %h", golden_ref.reg_file[4]);
$display("RF[5]: %h", golden_ref.reg_file[5]);
$display("RF[6]: %h", golden_ref.reg_file[6]);
$display("RF[7]: %h", golden_ref.reg_file[7]);
$display("PSR: %b", golden_ref.psr);
$display("VSR1: %h", golden_ref.reg_file[wbif.sr1]);
$display("VSR2: %h", golden_ref.reg_file[wbif.sr2]);
$display("");
$display("DUT Writeback Outputs:");
$display("enable_writeback: %b", wbif.enable_writeback);
$display("aluout: %h", wbif.aluout);
$display("memout: %h", wbif.memout);
$display("pcout: %h", wbif.pcout);
$display("npc: %h", wbif.npc);
$display("VSR1: %h", wbif.VSR1);
$display("VSR2: %h", wbif.VSR2);
$display("sr1: %b", wbif.sr1);
$display("sr2: %b", wbif.sr2);
$display("dr: %b", wbif.dr);
$display("psr: %b", wbif.psr);
$display("W_Control: %b", wbif.W_Control);
$display("========================================================");

endtask

function reset_chk();
  if(wbif.reset == 1) begin
    if(wbif.sr1 != 3'd0) begin
      $display($time, "[TB][WB][SR1]:[Value from DUT: %d][Value from GR: 0]", wbif.sr1);
	  wb_err++;
    end
    if(wbif.sr2 != 3'd0) begin
      $display($time, "[TB][WB][SR2]:[Value from DUT: %d][Value from GR: 0]", wbif.sr2);
	  wb_err++;
    end
  end
endfunction

function int rf_golden_ref_chk();
  if(wbif.VSR1 != golden_ref.reg_file[wbif.sr1]) begin
    $display($time, "[TB][WB][VSR1]:[Value from DUT: %h][Value from GR: %h]", wbif.VSR1, golden_ref.reg_file[wbif.sr1]);
    wb_err++;
  end
  if(wbif.VSR2 != golden_ref.reg_file[wbif.sr2]) begin
    $display($time, "[TB][WB][VSR2]:[Value from DUT: %h][Value from GR: %h]", wbif.VSR2, golden_ref.reg_file[wbif.sr2]);
    wb_err++;
  end
endfunction

function rf_golden_ref_update();
  if(wbif.enable_writeback)
    case(wbif.W_Control)
	  2'b00: golden_ref.reg_file[wbif.dr]=wbif.aluout;
	  2'b01: golden_ref.reg_file[wbif.dr]=wbif.memout;
	  2'b10: golden_ref.reg_file[wbif.dr]=wbif.pcout;
	  default: begin
	    golden_ref.reg_file[wbif.dr]=16'hxxxx;
		$display($time, "[TB][WB][W_Control]:[Value from DUT: %d][Value from GR: 0-2]", wbif.W_Control);
	    wb_err++;
	  end
	  endcase
	golden_ref.VSR1=golden_ref.reg_file[wbif.sr1];
	golden_ref.VSR2=golden_ref.reg_file[wbif.sr2];
	return 0;
endfunction

function psr_golden_ref_update();
  if(wbif.enable_writeback) 
    casex(golden_ref.reg_file[wbif.dr])
	    16'h0000: golden_ref.psr=3'b010;
	    16'b1xxxxxxxxxxxxxxx: golden_ref.psr=3'b100;
	    16'b0xxxxxxxxxxxxxxx: golden_ref.psr=3'b001;
	    default: begin
	      golden_ref.psr=3'bxxx;
		  $display($time, "[TB][WB][Golden_Ref]:[Value from GR: %d]", golden_ref.reg_file[wbif.dr]);
		  wb_err++;
	    end
	endcase
  return 0;
endfunction
	
function psr_chk();
  if(golden_ref.psr != wbif.psr) begin
    $display($time, "[TB][WB][PSR]:[Value from DUT: %d][Value from GR: %d]", wbif.psr, golden_ref.psr);
    wb_err++;
  end
endfunction
endclass
