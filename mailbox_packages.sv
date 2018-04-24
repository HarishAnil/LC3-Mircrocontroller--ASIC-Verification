	typedef struct packed {
		logic [15:0] npc;
		logic [15:0] pc;
		logic instrmem_rd;
	} fetch_out_sig;

typedef struct packed {
   logic [15:0]IR;
   logic [5:0]E_Control;
   logic [15:0]npc_out;
   logic Mem_Control;
   logic [1:0]W_Control;
} decode_out_sig;

typedef struct {
  logic [15:0] reg_file [7:0];
  logic [2:0] psr;
	logic [15:0] VSR1, VSR2;
} wb_out_sig;

typedef struct packed {
  logic [15:0] DMem_addr;
  logic [15:0] DMem_din;
  logic DMem_rd;
  logic [15:0] memout;
} mem_access_out_sig;

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
	} exe_out_sig;