#!/bin/bash

for file in \
theories/Base.v \
theories/Dependent_Function.v \
theories/Function.v \
theories/Dependent_Product.v \
theories/Dependent_Sum.v \
theories/Product.v \
theories/Sum.v \
theories/Void.v \
theories/Unit.v \
theories/W_type.v \
theories/Universe.v \
theories/Path.v \

do
  echo -n " ${file}"
done
