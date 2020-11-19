#!/bin/bash

# 私の環境に固有の設定であるが、めんどくさいため消さない
COQ_PATH=/c/coq

PATH=$COQ_PATH/bin:$PATH

coqdoc \
  -utf8 \
  -d docs \
  -R theories/ GiC \
  theories/Base.v \
  theories/Main.v
