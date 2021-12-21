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
theories/Dependent_Function_Path.v \
theories/Function_Path.v \
theories/Dependent_Product_Path.v \
theories/Dependent_Sum_Path.v \
theories/Product_Path.v \
theories/Sum_Path.v \
theories/Unit_Path.v \
theories/W_type_Path.v \
theories/Universe_Path.v \
theories/Path_Path.v \
theories/Dependent_Pointwise_Path.v \
theories/Pointwise_Path.v \
theories/Pointwise_Path_Pointwise_Path.v \

do
  echo -n " ${file}"
done
