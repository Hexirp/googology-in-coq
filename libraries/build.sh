#!/bin/bash

for file in $(./files.sh)
do
  ./coqc.sh -nois -verbose -R theories/ GiC ${file}
done
