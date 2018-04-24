##ECE_745_2018 Compile Script

vlog ./LC3_cleanDUT/*.vp
vlog ./LC3_cleanDUT/*.v

vlog -sv macros.sv
vlog -sv mailbox_packages.sv
vlog -sv interface_all.sv
vlog -sv controller_block_test.sv
vlog -sv fetch.sv
vlog -sv writeback.sv
vlog -sv decode.sv
vlog -sv execute.sv
vlog -sv mem_access.sv
vlog -sv Instruction_Mem.sv
vlog -sv verif_classes.sv
vlog -sv driver.sv
vlog -sv top_testbench.sv
vlog -sv coverage.sv


vsim  -novopt -sv_seed 1000 -coverage top 

##add wave -position insertpoint sim:/top/LC3_DUT/Ex/*
##add wave -position insertpoint sim:/top/LC3_DUT/MemAccess/*
##add wave -position insertpoint sim:/top/LC3_DUT/WB/*
##add wave -position insertpoint sim:/top/LC3_DUT/Fetch/*
##add wave -position insertpoint sim:/top/LC3_DUT/Ctrl/*

run -all
