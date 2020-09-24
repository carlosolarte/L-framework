
The L-Framework uses rewrite- and narrowing-based reasoning for proving crucial
properties of sequent systems such as admissibility of structural rules,
invertibility of rules and cut-elimination. Such procedures have been fully
mechanized in
[Maude](http://maude.cs.illinois.edu/w/index.php/The_Maude_System), achieving a
great degree of automation when used on several sequent systems including
intuitionistic and classical logics, linear logic, and normal modal logics. 

## Getting started

The project was tested in [Maude
3.0](http://maude.cs.illinois.edu/w/index.php/Maude_download_and_installation).
No extra library is needed for execution. The tool produces
[LaTeX](https://en.wikipedia.org/wiki/LaTeX) files with the results. 

## Structure of the project

The root directory contains the Maude files specifying the different procedures
and analyses. The directory `examples` contains case studies including systems
for classical and intuitionistic logic as well as modal and
substructural logics. 


## Documentation

Further documentation about the procedures implemented is available in the
header of each file.  See also [this
paper](https://link.springer.com/chapter/10.1007/978-3-319-99840-4_7) for
details on how the properties of sequent systems are encoded as rewriting logic
theories. 

## Case Studies

The directory `examples` contains several case studies. In each case, the
following files can be found:

- `logic.maude`: defining the syntax and inference rules of the sequent system
  considered.

- `prop-XXX.maude`: instantiating the different analyses. 

- `exec.maude`: Maude file that executes all the analyses. 

- `logic.tex`: main LaTeX file importing the output of different analyses. 

### Running the case studies

Go to the directory of one of the case studies and execute the Maude
interpreter on the file `exec.maude`:

```
$> cd examples/g3c
$> maude exec.maude

		     \||||||||||||||||||/
		   --- Welcome to Maude ---
		     /||||||||||||||||||\
	     Maude 3.0 built: Dec 17 2019 12:08:10
	     Copyright 1997-2019 SRI International
		   Thu Sep 24 15:33:15 2020
Proof of Height preserving admissibility of weakening on the left
*************************************************
Proving the case impR	......	[OK]
...
```

The bash `examples/exec.sh` runs all the case studies. 

## Results

Here the results for the case studies considered so far:

- [g3c](g3c.pdf): Two-sided system for classical propositional logic.

- [g3i](g3i.pdf): Two-sided, single-conclusion system for intuitionistic propositional
  logic.

- [mLJ](mLJ.pdf): Two-sided, multiple-conclusion system for intuitionistic
  propositional logic.

- [MALL](MALL.pdf): One-sided system for multiplicative-additive linear logic.

- [LL](LL.pdf): One-sided system for linear logic (with exponentials)

- [DyLL](DyLL.pdf): Dyadic system for linear logic

- [K](K.pdf): Model logic K

- [S4](S4.pdf): Modal logic extending K with the axioms T and 4

- [KT45](KT45.pdf): Modal logic extending K with the axioms T,4 and 5. Cut
  elimination does not hold for this logic

## Interested in defining a new case study?

See this step-by-step [tutorial](tutorial.md) explaining how to define a
sequent system and prove its properties. 
