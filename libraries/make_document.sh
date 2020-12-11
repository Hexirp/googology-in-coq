#!/bin/bash

./coqdoc.sh \
  -utf8 \
  -d docs \
  -R theories/ GiC \
  theories/Base.v \
  theories/Function.v \
  theories/Path/Base.v \
  theories/Path/Function.v \
  theories/Path/OneDim.v \
  theories/Path/Transposition.v \
  theories/Path/Functoriality.v \
  theories/Path/Application_1_0.v \
  theories/Path/Application_1_1.v \
  theories/Path/Transport.v \
  theories/Path/Fibration.v \
  theories/Path/Transport_2.v \
  theories/Path/Application_D.v \
  theories/Path.v \
  theories/Main.v
