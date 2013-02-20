#! /bin/sh

bin="${1%.exe}"
log="$2"

../cross_eval_machines ${bin}.exe ${bin}.types.canon ${bin}.bcg ${bin}.db ${log}/pre_machine ${log}/pre_mai ${log}/post_machine ${log}/post_mai ${log}/opt
