#!/bin/bash

set -e

./compile.sh

mkdir -p docs/

./coqdoc.sh -utf8 -d docs -R theories/ Googology_In_Coq $(./files.sh)

rm docs/coqdoc.css
cp coqdoc/default.css docs/coqdoc.css

set +e
