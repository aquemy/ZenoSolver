#!/bin/bash

texfile=ppsn2014

texgen=pdflatex
bibgen=bibtex

picdir=./pictures

## DO NOT EDIT AFTER THIS LINE ##

$texgen $texfile
$bibgen $texfile 
$texgen $texfile
$texgen $texfile

rm *.aux *.bbl *.blg *.log
#rm $picdir/*.pdf
