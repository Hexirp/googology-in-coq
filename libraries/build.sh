#!/bin/bash

set -e

for file in $(./files.sh)
do
  ./coqc.sh -nois -verbose -R theories/ GiC ${file}
done

set +e
