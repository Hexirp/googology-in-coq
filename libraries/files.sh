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
theories/W_type_Beta.v \
theories/W_type_Alpha.v \
theories/W_type.v \
theories/Universe.v \
theories/Path.v \
theories/Dependent_Pointwise_Path.v \
theories/Pointwise_Path.v \
theories/Pointwise_Path_Pointwise_Path.v \
theories/Section.v \
theories/Is_Half_Adjoint.v \
theories/Is_Half_Adjoint_Equivalence.v \
theories/Naive_Functional_Extensionality.v \
theories/Bool.v \
theories/Peano_Number_Tag.v \
theories/Peano_Number_Arity_Zero.v \
theories/Peano_Number_Arity_Successor.v \
theories/Peano_Number_Arity.v \
theories/Peano_Number.v \

do
  echo -n " ${file}"
done
