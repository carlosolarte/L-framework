# Examples of logical systems

In each of the following systems the following analyses are performed:
 - Admissibility of structural rules (Weakening and Contraction)
 - Invertibility of Rules
 - Proof of the Cut-Elimination theorem 
 - Proof of the Identity-Expansion theorem 

The systems considered are:
- __g3c__: Two-sided system for classical propositional logic. 

- __g3i__: Two-sided, single-conclusion system for intuitionistic propositional
  logic.

- __mLJ__: Two-sided, multiple-conclusion system for intuitionistic
  propositional logic.

- __MALL__: One-sided system for multiplicative-additive linear logic.

- __LL__: One-sided system for linear logic (with exponentials)

- __DyLL__: Dyadic system for linear logic

- __K__: Model logic K

- __S4__: Modal logic extending K with the axioms T and 4

- __KT45__: Modal logic extending K with the axioms T,4 and 5. Cut elimination
  does not hold for this logic


The file `commands.sty` contains common LaTeX macros used in the output of the
analyses. 

## Structure of the Examples

All the examples and directories follow the same pattern. Consider for instance
the system g3c:

 - `g3c.maude`: defines the syntax of the logic as well as the inference rules

 - `prop-XXX.maude`: fulfills the requirements for using the corresponding
   analysis.

 - `exec.maude`: executes all the analyses and generates the LaTeX output for
   each one.

 - `g3c.tex`: main LaTeX document calling the different results of the analyses.

