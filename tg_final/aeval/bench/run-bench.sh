#!/bin/bash
echo "This is the script for running regression tests"
echo " - date: $(date '+%Y-%m-%d at %H:%M.%S')"
echo " - host name $(hostname -f)"
echo " - script path: $(readlink -f $0)"

adtchc=../adtchc
if [[ ! $# -eq 0 ]] ; then
    #echo 'Setting path to' $1
    adtchc=$1
fi

# run the interpolating version of OpenSMT
adtchc=${adtchc}' -i'

picky=./utils/picky.smt2
lookahead=./utils/lookahead.smt2

tmpfolder=log-$(date '+%Y-%m-%d-%H-%M-%S')
mkdir ${tmpfolder}

export outmod=false
export errmod=false
export rtmod=false
export err=false

for file in $(find . -name '*.smt2' |sort); do
    name=$(basename $file)
    dir=$(dirname $file)

    sh -c "ulimit -St 60; ${adtchc} $dir/$name > $tmpfolder/$name.out 2>$tmpfolder/$name.err.tmp" 2>/dev/null
    grep -v '^;' $tmpfolder/$name.err.tmp > $tmpfolder/$name.err

    if [ -s "$tmpfolder/$name.err" ]; then
        echo "stderr not empty for benchmark $file";
        err=true;
    fi


done
#echo "Stdout differs: ${outmod}, stderr differs: ${errmod}"

if [[ ${err} == true ]]; then
    echo "There were anomalies: check logs in ${tmpfolder}"
    exit 1
else
    rm -rf ${tmpfolder}
fi
