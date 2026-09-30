# Typed / modal / computational self-reference

Status: **parallel draft phase; not a v1.0 blocker.**

This branch should not count standard guarded-recursion theorems as new project
results merely because they are re-formalized. The phase is valuable only if it
sharpens the self-application threshold already isolated by the Lawvere/Kleene
modules.

## Core question

Which typed, partial, modal, or effectful forms of self-application are exactly
strong enough to recover a Lawvere/Kleene-style fixed-point phenomenon?

## Candidate axes

- typed partial evaluators;
- definedness / partiality effects;
- later or guarded modalities;
- effectful self-application;
- a bridge from guarded/typed representation to Kleene program-code recursion.

## Required acceptance

At least one theorem must identify a threshold with both directions or with a
necessity countermodel. Examples:

- a precise sufficient typed/effect condition for diagonalization;
- an ablation showing a weaker typed interface avoids the fixed-point result;
- a bridge proving when a typed evaluator can simulate the existing Kleene
  recursion interface.

Until such a theorem exists, this remains a draft research branch and does not
block the framework-morphism / guide-core mainline.
