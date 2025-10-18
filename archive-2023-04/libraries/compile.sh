#!/bin/bash

set -e

for file in $(./files.sh)
do
  ./coqc.sh -nois -verbose -R theories/ Googology_In_Coq ${file}
done

set +e
