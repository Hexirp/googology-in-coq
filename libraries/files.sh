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
theories/W_type_Alpha.v \
theories/W_type_Beta.v \
theories/W_type.v \
theories/Universe.v \
theories/Path.v \
theories/Dependent_Pointwise_Path.v \
theories/Pointwise_Path.v \
theories/Pointwise_Path_Pointwise_Path.v \
theories/Is_Half_Adjoint_Equivalence.v \
theories/Bool.v \
theories/Peano_Number_Alpha.v \
theories/Peano_Number_Beta_Zero.v \
theories/Peano_Number_Beta_Successor.v \
theories/Peano_Number_Beta.v \
theories/Peano_Number.v \

do
  echo -n " ${file}"
done
