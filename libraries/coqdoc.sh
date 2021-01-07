#!/bin/bash

COQ_PATH=$(./coq_path.sh)

PATH=$COQ_PATH/bin:$PATH

coqdoc "$@"
