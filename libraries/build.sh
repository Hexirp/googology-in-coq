#!/bin/bash

for file in \
  Base.v \
  Function.v \
  Path/Base.v \
  Path/Function.v \
  Path/OneDim.v \
  Path/Transposition.v \
  Path/Application_1_0.v \
  Path/Application_1_1.v \
  Path.v \
  Main.v
do
  ./coqc.sh -nois -verbose -R theories/ GiC theories/${file}
done
