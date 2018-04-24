package verif_classes;
	`include "writeback.sv"
	`include "mem_access.sv"
	`include "decode.sv"
	`include "fetch.sv"
	`include "Instruction_Mem.sv"
	`include "controller_block_test.sv"
	`include "execute.sv"
	`include "mailbox_packages.sv"
	`include "driver.sv"

  writeback write_back;
  mem_access mem_a;
  decode dec;
  fetch fet;
  Instr_Mem IR_Instmem;
  controller cntrl;
  execute exe;
	driver drive;
`include "coverage.sv"
  ALU_OPR_cg alu_cover;
  MEM_OPR_cg mem_cover;
  CTRL_OPR_cg ctrl_cover;
  OPR_SEQ_cg opr_seq_cover;

	//Mailbox Packages
	fetch_out_sig fet_pkt_dr,fet_pkt_rc, fetch_out;
	decode_out_sig dec_pkt_dr,dec_pkt_rc, decode_out;
	wb_out_sig wb_pkt_dr,wb_pkt_rc, wb_out;
	mem_access_out_sig mem_access_pkt_dr,mem_access_pkt_rc, mem_access_out;
	exe_out_sig exe_pkt_dr,exe_pkt_rc, exe_out;
endpackage: verif_classes
