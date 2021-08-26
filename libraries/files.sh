#!/bin/bash

for file in \
Base/Base.v \
Base/Function.v \
Base/Dependent_Function.v \
Base/Unit.v \
Base/Void.v \
Base/Product.v \
Base/Sum.v \
Base/Dependent_Product.v \
Base/Dependent_Sum.v \
Base.v \

do
  echo -n " theories/${file}"
done
