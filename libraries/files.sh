#!/bin/bash

for file in \
theories/Base.v \
theories/Dependent_Function.v \
theories/Function.v \
theories/Playground.v \

do
  echo -n " ${file}"
done
