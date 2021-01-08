#!/bin/bash

for file in \
  Base.v \
  Function.v \
  Path/Base.v \
  Path/Function.v \
  Path/OneDim.v \
  Path/Transposition.v \
  Path/Functoriality.v \
  Path/TwoDim.v \
  Path/Application_1_0.v \
  Path/Application_1_1.v \
  Path/Transport.v \
  Path/Fibration.v \
  Path/Transport_2.v \
  Path/Application_D.v \
  Path.v
do
  echo -n "theories/${file} "
done
