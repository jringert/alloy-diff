#!/bin/bash
timeout -k 0s 10m /usr/bin/time -f "%M kB; %C" java -jar v1.jar $1 $2 $3 withPred 2>> memory.log
