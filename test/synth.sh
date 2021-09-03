#!/bin/bash

if [ -z "${1}" ]; then
	echo "missing argument" >&2
	exit 1
fi

yosys -p "read_verilog ${1}.v; proc ; techmap; opt; write_blif ${1}.blif"
berkeley-abc -c "read_blif ${1}.blif; strash; write_cnf ${1}.cnf"
