#!/bin/bash

#PID=".`readlink /proc/self`"
PID=""

rm -f ./interaction$PID.txt
tee -a ./interaction$PID.txt | z3 -in -smt2 | tee -a ./interaction_out$PID.txt
