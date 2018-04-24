`timescale 10ns / 1ps
`include "macros.sv"
import verif_classes::*;
class driver;
int fetch_err_count=0;
int decode_err_count=0;
int writeback_err_count=0;
int mem_access_err_count=0;
int control_err_count=0;
int execute_err_count=0;
int prev_fetch_err=0, prev_decode_err=0, prev_execute_err=0, prev_writeback_err=0, prev_mem_access_err=0, prev_control_err=0;
int num_tests=0;
int num_failed_tests=0;
writeback write_back;
mem_access mem_a;
decode dec;
fetch fet;
controller cntrl;
execute exe;


function new(writeback write_back, mem_access mem_a, decode dec, fetch fet, controller cntrl, execute exe);
	this.write_back=write_back;
	this.mem_a=mem_a;
	this.dec=dec;
	this.fet=fet;
	this.cntrl=cntrl;
	this.exe = exe;
endfunction

task start_driver();
			fork
				fet.ft_check(fetch_err_count);
				dec.de_check(decode_err_count);
				write_back.wb_check(writeback_err_count);
				mem_a.ma_check(mem_access_err_count);
				cntrl.test_control(control_err_count);
				exe.execute_check(execute_err_count);
			join_none
endtask

task update_scoreboard();
	num_tests++;
	if(fetch_err_count==prev_fetch_err && decode_err_count==prev_decode_err && writeback_err_count==prev_writeback_err && control_err_count==prev_control_err && execute_err_count==prev_execute_err && mem_access_err_count==prev_mem_access_err)
		num_failed_tests=num_failed_tests;
	else
		num_failed_tests++;
		
	prev_fetch_err=fetch_err_count;
	prev_decode_err=decode_err_count;
	prev_writeback_err=writeback_err_count;
	prev_control_err=control_err_count;
	prev_execute_err=execute_err_count;
	prev_mem_access_err=mem_access_err_count;
endtask

task report_scoreboard();
	$display("");
	$display("");
	$display("********************Final Scoreboard Report********************");
	$display("Total Number of Tests:  %d", num_tests);
	$display("Number of Failed Tests: %d", num_failed_tests);
	$display("");
	$display("Error Breakdown by Module: ");
	$display("Fetch Errors:           %d", fetch_err_count);
	$display("Decode Errors:          %d", decode_err_count);
	$display("Writeback Errors:       %d", writeback_err_count);
	$display("Control Errors:         %d", control_err_count);
	$display("Execution Errors:       %d", execute_err_count);
	$display("Memory Access Errors:   %d", mem_access_err_count);
	$display("***************************************************************");
endtask: report_scoreboard

endclass;
