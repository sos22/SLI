#! /bin/bash

f="$1"
matches() {
    grep -q "$1" "$f"
}

result() {
    mkdir -p results/$1
    cp $f results/$1/$f
    exit 0
}

if matches "No proximal cause"
then
    if matches "Generated event load"
    then
	result "proximal_load_static"
    fi
    if matches "Generated event cas"
    then
	result "proximal_cas"
    fi
    if grep -q "$f:.*rep" ../../disassembly
    then
	result "proximal_string"
    fi
    result "proximal_none"
fi

if matches "No function for $f"
then
    result "no_function"
fi

if matches "timed out"
then
    result "timeout"
fi

if matches "Load machine:"
then
    if matches "decoder said not implemented"
    then
	result "generated_summary_decoder_failed"
    fi
    if matches "can't find an appropriate dominator"
    then
	result "generated_summary_no_dominator"
    fi
    result "generated_summary"
fi

if ! matches "Cluster:"
then
    result "no_store_machines"
fi

if matches "Don't know how to backtrack across CAS statement?"
then
    result "backtrack_cas"
fi

if matches "Couldn't find any relevant-looking races"
then
    result "no_races"
fi

result "unknown"
