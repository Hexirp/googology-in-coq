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
Base/Path.v \
Base/TYPE.v \
Base/Path_Reasoning.v \
Base/Pointwise_Path.v \
Base/Pointwise_Path_Reasoning.v \
Base/Equivalence.v \
Base.v \

do
  echo -n " theories/${file}"
done
