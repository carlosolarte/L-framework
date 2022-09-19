# L-Framework

The L-Framework uses rewrite-based reasoning for proving crucial properties of
sequent systems such as admissibility of structural rules, invertibility of
rules and cut-elimination. Such procedures have been fully mechanized in
[Maude](http://maude.cs.illinois.edu/w/index.php/The_Maude_System), achieving a
great degree of automation when used on several sequent systems including
intuitionistic and classical logics, linear logic, and normal modal logics. 

## Getting started

The project was tested in [Maude
3.2](http://maude.cs.illinois.edu/w/index.php/Maude_download_and_installation).
No extra library is needed for execution. The tool produces
[LaTeX](https://en.wikipedia.org/wiki/LaTeX) files with the results. 

## Structure of the project

The root directory contains the Maude files specifying the different procedures
and analyses. The directory [examples](./examples) contains case studies
including systems for classical and intuitionistic logic as well as modal and
substructural logics. Further documentation about the procedures implemented
can be found in [docs](./docs).
