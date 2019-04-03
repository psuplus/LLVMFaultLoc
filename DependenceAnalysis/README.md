This is a field-sensitive dataflow- and control-flow dependence analysis. The
implementation is based on llvm-deps, a PDG implementation, developed by Scott
Moore at Harvard University, and DSA, a points-to analysis, developed by Will
Dietz, Joshua Cranmer, Matthew Wala at UIUC.

## Build

Run "./configure" and "make"

## Use the dependence analysis

The folder "sensitivity-tests" contains a variety of unit-tests with expected
outputs. Run "test.sh" will unit test on all of those files.

We use to illustrate how to use our analysis on one c file.

1. Navigate to 'addr_tes' folder
2. taint.txt and untrust.txt specify the "source" variables for the dependence
analysis (in most cases, they are the same)
3. the script "run.sh" runs the dependence analysis. Here are the results:

#--------------Results------------------

main.c line 16
main.c line 18
main.c line 20
main.c line 22

By default, the analysis outputs all branches that are dataflow-dependent on
the sources. The tool can also be configured to consider controlflow dependence
and any instruction in the source code.

## processing_tools

Scripts to help parse the raw data produced by the analysis.

## Acknowledgments

This project is supervised by Danfeng Zhang at the Pennsylvania State
University, Department of Computer science and engineering.

The development and maintenance of this software has been supported by by a
grant from the National Science Foundation (CCF-1566411). Adam Mohammed
prepared the release and implemented the filed-sensitivity analysis. Peixuan
Li, Xiang Li, Haojun Sui have also helped in the software development.
