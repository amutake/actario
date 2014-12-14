#!/usr/bin/env bash

# 1. make patch
# 2. download coq and apply patch

scriptname="patch.sh"
prefix="coq-"
suffix="+actor"

cd `dirname $0`

original=${prefix}${2}
patched=${prefix}${2}${suffix}
patch_file=${2}.patch

case "$1" in
    "make")
        if [ "$2" = "" ]; then
            echo "Please specify the Coq version"
            echo "e.g., ./${scriptname} make 8.4pl5"
        elif [ -d ${original} ] && [ -d ${patched} ]; then
            diff -u -N -r ${original} ${patched} > ${patch_file}
        else
            echo "${original} and ${patched} are required"
        fi
        ;;
    "apply")
        if [ "$2" = "" ]; then
            echo "Please specify the Coq version"
            echo "e.g., ./${scriptname} apply 8.4pl5"
        elif [ -d ${original} ] && [ -f ${patch_file} ]; then
            if [ -d ${patched} ]; then
                echo -n "${patched} exists. It will be replaced to patched Coq. OK? [y/N]"
                read ok
                if [ "$ok" = "y" ] || [ "$ok" = "Y" ]; then
                    rm -rf ${patched}
                    cp -r ${original} ${patched}
                    patch -u -p1 -d ${patched} < ${patch_file}
                else
                    echo "aborted."
                fi
            else
                cp -r ${original} ${patched}
                patch -u -p1 -d ${patched} < ${patch_file}
            fi
        else
            echo "${original} and ${patch_file} are required"
        fi
        ;;
    "auto")
        echo "not supported yet"
        ;;
    *)
        echo "Usage: ${scriptname} <command> <args>"
        echo ""
        echo "Commands:"
        echo "  make  <version>    - make patch file"
        echo "  apply <version>    - apply patch to Coq"
        echo "  auto  <version>    - auto download, apply, install"
        ;;
esac
