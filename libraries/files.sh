#!/bin/bash

for file in \
Base/Base.v \
Base/Function.v \
Base/Dependent_Function.v \
Base/Unit.v Base/Void.v \
Base.v \

do
  echo -n " theories/${file}"
done
