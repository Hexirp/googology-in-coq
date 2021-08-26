#!/bin/bash

for file in Base/Base.v Base/Function.v Base/Dependent_Function.v Base.v
do
  echo -n " theories/${file}"
done
