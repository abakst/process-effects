#!/usr/bin/env bash

EXTRACT="stack exec -- liquid --idirs=$PWD/../include"
SPIN="spin" 
PAN="spin -run -safety" 

OPTIND=1
set -e

bench_file=1
pan_flags=""
simulate=1

while getopts "sp:" opt; do
    case "$opt" in
        s)
            simulate=0
            ;;
        p) pan_flags="$OPTARG"
           ;;
    esac
done

shift $(($OPTIND - 1))
bench_file="$1"

if [ -z "$pan_flags" ]; then
    pan_flags="-DVECTORSZ=16384 -DSFH -DNOBOUNDCHECK -DSAFETY -DNOCOMP -DNOFAIR -DNOSTUTTER"
fi

if [[ ! -f "$bench_file" ]]; then
    echo "File $bench_file does not exist or is not a regular file"
    exit 1
fi

${EXTRACT} ${bench_file} &>/dev/null

status=$?
if [[ ! $status ]]; then
    echo "Error running $cmd"
fi

bench_file_promela="$(dirname $bench_file)/.liquid/out.pml"
if [ -f "out.pml.trail" ]; then
    rm "out.pml.trail"
fi

if [ $simulate ]; then
  ${SPIN} ${pan_flags} "$(dirname $bench_file)/.liquid/out.pml"
else
  ${PAN} ${pan_flags} "$(dirname $bench_file)/.liquid/out.pml"
fi

if [ -f "out.pml.trail" ]; then
    exit 1
else
    rm -f pan
fi
