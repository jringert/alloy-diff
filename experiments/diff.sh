#!/bin/bash
# compute diff statistics with a timeout of 10min for each pair of specs
timeout -k 0s 10m /usr/bin/time -f "%M kB; %C" java -jar diff.jar $1 $2 $3 withPred 2>> memory.log
# use the next line to produce statistics for single models (first parameter)
#timeout -k 0s 10m /usr/bin/time -f "%M kB; %C" java -jar v1.jar $1 $2 $3 withPred 2>> memory.log
