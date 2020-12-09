#!/bin/bash

# 私の環境に固有の設定であるが、面倒なので、一般の環境に対して対応はしない。
COQ_PATH=/c/coq

PATH=$COQ_PATH/bin:$PATH

coqc "$@"
