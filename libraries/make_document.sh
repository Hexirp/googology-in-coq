#!/bin/bash

./build.sh

./coqdoc.sh -utf8 -d docs -R theories/ GiC $(./files.sh)

rm docs/coqdoc.css
cp coqdoc/default.css docs/coqdoc.css
