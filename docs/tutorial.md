This tutorial shows how to define the syntax and inference rules for a
sequent-based system and prove some properties such as admissibility of
structural rules (e.g., weakening and contraction), invertibility of rules,
identity expansion and cut elimination.

## Syntax and Rules

Everything starts with the definition of the syntax and the inference rules of
the sequent system.  Let us consider a two-sided, single-conclusion system for
intuitionistic propositional logic. The first step is to create a Maude file
with the following structure (see the complete set of files in `examples/g3i`). 

```
--- File g3i.maude

--- Loading the basic definitions
load ../../sequent .

--- Module defining the syntax and the inference rules
mod G3i is
    ex SEQUENT-SOLVING . --- Importing some modules

    --- Atomic Propositions of the form p(3)
    ops p : Nat -> Prop [ctor] .

    --- Conjunction
    op _/\_ : Formula Formula -> Formula [ctor  prec 30] .
    --- Disjunction
    op _\/_ : Formula Formula -> Formula [ctor  prec 30] .
    --- False
    op False : -> Formula [ctor] .
    --- True
    op True : -> Formula [ctor] .
    --- Implication
    op _-->_ : Formula Formula -> Formula [ctor prec 35] .


    --- The following two definitions maps operators of the syntax to LaTeX
    symbols (for pretty print)

    eq TEXReplacement =
	('|-- |-> '\vdash), ('/\ |-> '\wedge) , ('\/ |-> '\vee) ,
	('--> |-> '\iimp), ('; |-> '`, ), ('True |-> '\top),
	('False |-> '\bot)
	.

    eq TEXReplacementSeq =
	('AndL |-> '\wedge_L), ('AndR |-> '\wedge_R),
	('OrL |-> '\vee_L), ('OrR1 |-> '\vee_1), ('OrR2 |-> '\vee_2),
	('botL |-> '\bot_L), ('botR |-> '\bot_R),
	('topL |-> '\top_L), ('topR |-> '\top_R),
	('impL |-> '\iimp_L), ('impR |-> '\iimp_R)
	.

    --- Declaring some variables to write the inference rules
    var P : Prop .
    vars F G H : Formula .
    vars C1 C2 C C' : MSFormula .


    --- Specifying the inference rules
    rl [I] :     P ; C |-- P  => proved .
    rl [AndL] :  F /\ G ; C |-- H => F ; G ; C |-- H .
    rl [AndR] :  C |-- F /\ G  =>  ( C |-- F) | ( C |-- G) .
    rl [botL] :  C ; False |-- H => proved .
    rl [topR] :  C |-- True => proved .
    rl [topL] :  C ; True |-- H => C |-- H .
    rl [OrL] :   C ; F \/ G |-- H => (C ; F |-- H) | (C ; G |-- H) .
    rl [OrR1] :   C |-- F \/ G =>  C |-- F .
    rl [OrR2] :   C |-- F \/ G =>  C |-- G .
    rl [impR] :  C |-- (F --> G) => C ; F |-- G .
    rl [impL] :  C ; F --> G |-- H => ( C ; F --> G  |-- F ) | ( C ; G |-- H) .
endm
```

As it can be noticed, the specification of the sequent system is quite natural
and close to what we have in textbooks. Regarding the syntax, 

```
op _/\_ : Formula Formula -> Formula [ctor  prec 30] .
```

declares a binary operator (denoting conjunction of formulas). 

Rules are specified as rules that rewrite the conclusion into their premises.
If the rule has no premises, the constructor `proved` is used (denoting that
there is nothing left to be proved). See for instance the initial rule `[I]`.
Rules with two premises use the operator `_|_` to identify the two goals that
need to be proved (see e.g., the rule `[AndR]`). 

This module can be used to prove sequents in this logic. For instance, we can
build a derivation for the sequent `p(1) /\ p(2) |-- p(2) \/ p(1)` as follows:

```
$> maude g3i
Maude> search [1] p(1) /\ p(2) |-- p(2) \/ p(1) =>* proved .
search in G3i : p(1) /\ p(2) |-- p(2) \/ p(1) =>* proved .

Solution 1 (state 6)
states: 7  rewrites: 8 in 0ms cpu (0ms real) (69565 rewrites/second)
empty substitution

```

The rules applied in such derivation can be printed as follows (`6` is the
successful state reported by the command `search` above):

```
Maude> show path 6 .
state 0, Sequent: p(1) /\ p(2) |-- p(2) \/ p(1)
===[ rl C ; F /\ G |-- H => F ; C ; G |-- H [label AndL] . ]===>
state 1, Sequent: p(1) ; p(2) |-- p(2) \/ p(1)
===[ rl C |-- F \/ G => C |-- F [label OrR1] . ]===>
state 4, Sequent: p(1) ; p(2) |-- p(2)
===[ rl P ; C |-- P => proved [label I] . ]===>
state 6, Goal: proved
```

This trace shows that first the rule `[AndL]` was used, then `[OrR1]` and the
proof finished with an application of the initial rule. 

## Admissibility of Weakening

Let us prove that the following rule

```
Gamma |-- G
------------- W
Gamma,F |-- G
```

is height preserving admissible. This means that, if there is a proof of the
premise `Gamma |-- G` with height at most `n`, then, there is a proof of the
conclusion `Gamma, F |-- G` with height at most `n`.  

The following script configures the needed theory to prove the admissibility
theorem.

```
--- File: prop-W.maude

--- Loading the theory with the analysis
load ../../admissibility .

fmod ADMISSIBILITY-W is
  pr META-LEVEL .

  --- Name of the theorem
  op th-name : -> String .
  eq th-name = "Height preserving admissibility of weakening" .

  --- Identifier of the Module defining the sequent system
  op mod-name : -> Qid .
  eq mod-name = 'G3i .

  vars GT GT' GT'' : GroundTerm .

  --- Specification of the rule to be proved admissible
  op rule-spec : -> Rule .
  eq rule-spec
  = ( rl '_:_['n:FNat,  '_|--_['_;_['Gamma:MSFormula, 'F0:Formula], 'H:Formula]] 
     => '_:_['n:FNat, '_|--_['Gamma:MSFormula,'H:Formula]]
        [ label('W) ]. ) .

  --- Bound for the search procedure
  op bound-spec : -> Nat .
  eq bound-spec = 10 .

  --- Output file
  op file-name : -> String .
  eq file-name = "weakeningL.tex" .

  --- Invertibility is not needed for this result
  op inv-rules : -> QidList .
  eq inv-rules = nil .

  --- No mutual induction is needed
  op mutual-ind : GroundTerm -> RuleSet .
  eq mutual-ind(GT) = none .

  --- No previous theorems needed
  op already-proved-theorems : -> RuleSet .
  eq already-proved-theorems = none .
endfm

view Admissibility-W from ADMISSIBILITY-SPEC to ADMISSIBILITY-W is endv    

mod PROVE-W is pr  ADMISSIBILITY-THEOREM{Admissibility-W} . endm

```

All the parameters are self explanatory. The only interesting part is the
definition of the rule in the parameter `rule-spec`. This term corresponds to
the specification of the rule `W` (rewriting the conclusion into the premise).
This term may look strange at first sight, but it is nothing else that the
[meta
representation](http://maude.lcc.uma.es/maude30-manual-html/maude-manualch17.html#x98-21500017)
of the rule

```
rl [W] : Gamma, F |-- H => Gamma |-- H .
```

The property is proved as follows:

```
$> maude g3i
Maude> load prop-W .
Maude> erew prove-it .
```

Maude will check the admissibility of the rule `W` with respect to all the rules
of the system G3i:

```
Proof of Height preserving admissibility of weakening
*************************************************
Proving the case topR	......	[OK]
Proving the case impR	......	[OK]
Proving the case AndR	......	[OK]
Proving the case OrR1	......	[OK]
Proving the case OrR2	......	[OK]
Proving the case impL	......	[OK]
Proving the case AndL	......	[OK]
Proving the case OrL	......	[OK]
Proving the case botL	......	[OK]
Proving the case I	    ......	[OK]
Proving the case topL	......	[OK]
Done! ....... 	
Output: weakeningL.tex
```

The proof is written in the file `weakeningL.tex`.


## Invertibility of Rules

Checking the invertibility of rules requires to define some parameters for the
algorithm implementing the analysis. 

```
--- File: prop-inv.maude

load ../../invertibility .

fmod INV-G3i is
  pr META-LEVEL .
  op mod-name : -> Qid .
  eq mod-name = 'G3i .

  --- Bound of the search procedure
  op bound-spec : -> Nat .
  eq bound-spec = 10 .

  --- We assume that the Height theorem: 
  --- (if n|-- Gamma then s(n) |-- Gamma )
  --- and also admissibility of weakening 

  op already-proved-theorems : -> RuleSet .
  eq already-proved-theorems = 
  ( rl '_:_['suc['n:FNat],  '_|--_['Gamma:MSFormula, 'H:Formula]] =>
    '_:_['n:FNat, '_|--_['Gamma:MSFormula,'H:Formula]] [ label('height) ]. ) 
  ( rl '_:_['n:FNat,  '_|--_['_;_['F:Formula, 'Gamma:MSFormula], 'H:Formula]] =>
    '_:_['n:FNat, '_|--_['Gamma:MSFormula,'H:Formula]]
    [ label('W) ]. ) .

  op file-name : -> String .
  eq file-name = "inv.tex" .
endfm

view Inv-G3i from INV-SPEC to INV-G3i is endv    

mod PROVE-INV is pr   INV-PROVING{Inv-G3i} . endm

```

As it can be noticed, this result relies on two (already proved) theorems: the
admissibility of weakening and also the fact that, if it is possible to prove
the sequent `S` with `n` steps, then, it can be also proved with `S(n)` steps
(see `prop-H.maude`). The other parameters are self explanatory.

The following command executes the analysis:

```
$> maude g3i
Maude> load prop-inv .
Maude>  erew prove-it .

Proving the case topR:	    ......	[OK]
Proving the case impR:	    ......	[OK]
Proving the case AndR(L):	......	[OK]
Proving the case AndR(R):	......	[OK]
Proving the case OrR1:	    ......	[Fail]
Proving the case OrR2:	    ......	[Fail]
Proving the case impL(L):	......	[Fail]
Proving the case impL(R):	......	[OK]
Proving the case AndL:	    ......	[OK]
Proving the case OrL(L):	......	[OK]
Proving the case OrL(R):	......	[OK]
Proving the case botL:	    ......	[OK]
Proving the case I:	        ......	[OK]
Done! .......
Output: inv.tex

```

For rules with two premises, it is possible to analyze whether one of the
premises is invertible. For instance, in this system, the right premise of
Implication-Left is invertible (but its left premise is not). 

## Identity-Expansion

Now we shall prove that, for any formula `F`, the sequent `F |-- F` is provable
in the system. 

```

--- File: prop-ID.muade

load ../../id-expand .

fmod ID-EXP is
    pr META-LEVEL .

    op mod-name : -> Qid .
    eq mod-name = 'G3i .

    op file-name : -> String .
    eq file-name = "id-exp.tex" .

    op bound-spec : -> Nat .
    eq bound-spec = 10 .

    var F : GroundTerm .
    op goal : GroundTerm -> GroundTerm .
    eq goal(F) = '_:_['inf.INat, '_|--_[F, F]] .

    op already-proved-theorems : -> RuleSet .
    eq already-proved-theorems
    = ( rl '_:_['inf.INat, '_|--_['_;_['Gamma:MSFormula, 'GW:Formula], 'Delta:MSFormula]] =>
            '_:_['inf.INat, '_|--_['Gamma:MSFormula,'Delta:MSFormula]] [ label('W) ]. ) .

    op types-formula : -> TypeList .
    eq types-formula = nil .
endfm

view Id-EXP from ID-EXP-SPEC to ID-EXP is endv

mod PROVE-ID is pr  ID-EXP-THEOREM{Id-EXP} . endm

```

The parameter `goal` defines the sequent to be proved: for any formula `F`, we
are interested in showing that `F |-- F` is provable. Here, the
meta-representation of this sequent must be used. This result depends on the 
admissibility of weakening. 

The analysis is executed as follows:

```
$> maude g3i
Maude> load prop-ID .
Maude> erew prove-it .
Identity expansion
*************************************************
Done! ....... 	[All cases proved]
Output: id-exp.tex
```

## Proving Cut-Elimination

There are different instances for the cut-elimination procedure. In this
directory, it is possible to prove that the multiplicative (splitting the
context) and the additive (sharing the context) cut rules are admissible. See,
respectively, the files `prop-cut-lin.maude` and `prop-cut.maude`. 

Consider the additive case:

```
--- File: prop-cut.maude

--- Additive procedure for single conclusion systems
load ../../cut-add-scon.maude

fmod CUT-G3i is
    pr META-LEVEL .
    op mod-name : -> Qid .
    eq mod-name = 'G3i .
    --- Bound of the search procedure
    op bound-spec : -> Nat .
    eq bound-spec = 15 .

    --- We assume the theorem on heights
    op already-proved-theorems : -> RuleSet .
    eq already-proved-theorems =
	( rl '_:_['suc['n:FNat],  '_|--_['Gamma:MSFormula, 'F:Formula]] =>
        '_:_['n:FNat, '_|--_['Gamma:MSFormula,'F:Formula]] [ label('H) ]. ) .

    --- File name to write the output
    op file-name : -> String .
    eq file-name = "cut.tex" .

    --- Inveretibilities are needed
    op inv-rules : -> QidList .
    eq inv-rules = 'AndL 'OrL 'impL$$1 .
endfm

view Cut-G3i from CUT-SPEC to CUT-G3i is endv

mod PROVE-CUT is pr CUT-PROVING{Cut-G3i} . endm

```

In this proof, it is used the fact that, if it is possible to prove the sequent
`S` with `n` steps, then, it can be also proved with `S(n)` steps (see
`prop-H.maude`). 

The analysis is executed as follows:

```
$> maude g3i
Maude> load prop-cut .
Maude> erew prove-it .
Cut Elimination Theorem
*************************************************
Cut-elimination Theorem
Proving the case topR	......	[OK]
Proving the case impR	......	[OK]
Proving the case AndR	......	[OK]
Proving the case OrR1	......	[OK]
Proving the case OrR2	......	[OK]
Proving the case impL	......	[OK]
Proving the case AndL	......	[OK]
Proving the case OrL	......	[OK]
Proving the case botL	......	[OK]
Proving the case I	......	[OK]
Proving the case topL	......	[OK]
Done! .......
Output: cut.tex
```

