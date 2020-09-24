#!/bin/bash

MAUDE="maude -no-wrap -batch -no-advise -no-banner"
LATEX=pdflatex

comp_ex(){
 name=$1
 echo "Processing..." $name
 $MAUDE $name/exec > $name.log 2>&1
 cd $name
 echo "Generating PDF..." $name
 $LATEX $name > /dev/null 2>&1
 $LATEX $name > /dev/null 2>&1
 echo "Done...." $name
}

comp_ex "K" &
comp_ex "S4" &
comp_ex "KT45" &
comp_ex "g3c" &
comp_ex "g3i" &
comp_ex "mLJ" &
comp_ex "LL" &
comp_ex "MALL" &
comp_ex "DyLL" 
wait

