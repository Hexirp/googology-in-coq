#!/bin/bash

for file in \
theories/Base.v \
theories/Dependent_Function.v \
theories/Function.v \
theories/Path.v \
theories/Void.v \
theories/Unit.v \
theories/Sum.v \
theories/Product.v \
theories/Dependent_Sum.v \
theories/Dependent_Product.v \
theories/Based_Path.v \
theories/Playground.v \

do
  echo -n " ${file}"
done
