# Distinction / Self-Reference in Lean

A small formal research project for studying which additional conditions turn a minimal distinction-and-reentry system into progressively stronger forms of self-reference.

The project deliberately separates:

1. **Established results** from the literature and existing formalizations.
2. **Small executable/formal models** that isolate one condition at a time.
3. **Conjectures / research targets** that are not yet proved.

The first milestone starts from the weakest concrete crossing model we can test without pretending that it is the unique meaning of “distinction”.

## Initial questions

- What is the weakest structure needed to represent a distinction?
- When does re-entry mean a static fixed point, and when is it better represented dynamically?
- Which extra conditions force fixed points?
- Which extra conditions create new states rather than contradictions?
- Can different self-reference frameworks be compared by implication / interpretation?
- Is there a useful notion of a minimal sufficient self-reference meta-framework?

## Status

Bootstrap in progress. The first research branch will add Lean models, CI, and literature notes.

## Scope warning

The code in this repository is **not** initially a formalization of all of Spencer-Brown's *Laws of Form* or Varela's calculus. Small models may be inspired by those ideas, but such relationships will be stated explicitly and conservatively.
