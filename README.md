A fault localization framework built on LLVM
============================================

This directory and its subdirectories contain source code for a general fault
localization framework. There are two major components:

## Fault localization (folder "FaultLocalization")

A general framework that allows logging program execution at different levels
of granularity (e.g., statements, basic blocks), as well as localizing the most
likely faults in the source code, based on a probabilistic reasoning model.

## Dependence analysis (folder "DependenceAnalysis")

A precise context-sensitive, field-sensitive dependence analysis. The analysis
takes arbitrary program variables as sources and returns all program statements
that are dataflow and/or controlflow dependent on the sources. While the
dependent analysis was designed to be general purpose, the results can be
utilized by the fault localization to improve its accuracy.

Go to those folders for more details.

## Compatibility

We have tested on Ubuntu 16.04 and MacOS 10.14.3. On MacOS above 10.14,
/usr/include is removed. But it can be recovered by the following package:
/Library/Developer/CommandLineTools/Packages/macOS_SDK_headers_for_macOS_10.14.pkg 
