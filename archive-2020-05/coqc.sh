#!/bin/bash

COQ_PATH=/c/coq # 私の環境に固有の設定であるが、めんどくさいため消さない

PATH=$COQ_PATH/bin:$PATH

coqc -nois "$@"
