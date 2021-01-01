#!/bin/bash

for file in $(./files.sh)
do
  ./coqdoc.sh -utf8 -d docs -verbose -R theories/ GiC theories/${file}
done
