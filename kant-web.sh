#!/bin/sh
export kant_datadir=`pwd`/data
./dist/build/kant-web/kant-web "$@"
