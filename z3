#!/bin/bash

#PID=".`readlink /proc/self`"
PID=""

rm -f ./interaction$PID.txt
rm -f ./interaction_out$PID.txt
tee -a ./interaction$PID.smt2 | z3 -in -smt2 | tee -a ./interaction_out$PID.smt2
