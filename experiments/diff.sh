#!/bin/bash
# compute diff statistics with a timeout of 10min for each pair of specs
#/usr/bin/time -f "%M kB; %C" timeout -k 0s 10m java -jar diff.jar $1 $2 $3 withPred 2>> memory.log
# use the next line to produce statistics for single models (first parameter)
/usr/bin/time -f "%M kB; %C" timeout -k 0s 10m java -jar v1.jar $1 $2 $3 withPred 2>> memory.log
