typex
=====

XPath formalisation, Alternating automata...

Requirements:
=============

- Containers library by S. Lescuyer: Finite sets and maps library. 
  Available from the coq contribs.
  Should be setup in your ~/.coqrc as:
<<
Add ML Path "PATH_TO_CONTRIBS/Orsay/Containers/src/".
Add Rec LoadPath "PATH_TO_CONTRIBS/Orsay/Containers/theories/" as Containers.
>>

To compile:
# coq_makefile -f Make -o Makefile
# make

