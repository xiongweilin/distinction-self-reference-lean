# Established results relevant to distinction and self-reference

This file separates established mathematics from experiments in this repository.

## 1. Spencer-Brown: distinction, calling, crossing

George Spencer-Brown's *Laws of Form* (1969) starts from a distinction and develops a calculus of indications. Two central arithmetic laws are usually called the **law of calling** and the **law of crossing**.

For this repository, the important conservative extraction is only:

- crossing can be modeled as an involutive operation in the smallest semantic models;
- this does **not** by itself formalize the full primary arithmetic or primary algebra.

References:

- G. Spencer-Brown, *Laws of Form*, 1969.
- Oxford Handbook discussion of the calling and crossing laws:
  https://academic.oup.com/edited-volume/28359/chapter-abstract/215235298

## 2. Varela: self-reference and a third state

Francisco Varela's 1975 paper extends the calculus of indications to self-reference. Its abstract explicitly describes a third state that arises through self-indication.

Reference:

- F. J. Varela, "A Calculus for Self-Reference", *International Journal of General Systems* 2(1), 1975, pp. 5-24.
  https://doi.org/10.1080/03081077508960828

Important scope note: the three-state model in this repository is only a minimal fixed-point experiment. It is not yet a formalization of Varela's calculus.

## 3. Schwartz isomorphism results

Daniel G. Schwartz (1981) established exact translations/isomorphisms into more standard logical notation:

- Spencer-Brown's primary algebra is described as essentially isomorphic to classical propositional calculus.
- Varela's calculus for self-reference is translated isomorphically into an axiomatization of S. C. Kleene's three-valued logic of partial recursion.

Reference:

- D. G. Schwartz, "Isomorphisms of Spencer-Brown's Laws of Form and Varela's Calculus for Self-Reference", *International Journal of General Systems* 6(4), 1981, pp. 239-255.
  https://doi.org/10.1080/03081078108934802

This is a particularly important bridge target for formalization because it gives a concrete way to test whether a future Lean encoding of the primary algebra or Varela calculus has captured the intended equational theory.

## 4. Lawvere fixed-point theorem

Lawvere's diagonal/fixed-point theorem provides a highly general mechanism by which sufficient internal representability forces fixed points.

There are two directly useful Lean routes:

- Mathlib's `Function.exists_fixed_point_of_surjective`, documented as an instance of Lawvere's fixed-point theorem for types and functions.
- Matthew Nestor's categorical Lean 4 formalization:
  https://github.com/mdnestor/LawvereFixedPoint

The file `DistinctionSelfReference/Representational.lean` reuses the Mathlib theorem to keep the first bridge minimal.

## 5. Knaster-Tarski fixed-point theorem

For a monotone endomap on a complete lattice, the fixed points form a complete lattice. In particular, least and greatest fixed points exist.

This is already formalized in Mathlib:

- `Mathlib.Order.FixedPoints`
- `fixedPoints.completeLattice`
- `OrderHom.lfp` / `OrderHom.gfp`

The file `DistinctionSelfReference/OrderTheoretic.lean` deliberately reuses this existing theorem instead of reproving it.

## 6. Rogers and Kleene computability fixed points

Mathlib already formalizes program-code self-reference in `Mathlib.Computability.PartrecCode`:

- `Nat.Partrec.Code.fixed_point`: Rogers' fixed-point theorem.
- `Nat.Partrec.Code.fixed_point₂`: Kleene's second recursion theorem.

These are computability-theoretic forms of self-reference: computable transformations of program descriptions have extensional/behavioral fixed points. They are conceptually different from:

- a literal state fixed point x = f(x);
- a period-two dynamic orbit;
- an order-theoretic least fixed point.

The file `DistinctionSelfReference/Computability.lean` exposes both results as an explicit framework branch.

## 7. Working classification

For this project, established self-reference mechanisms are provisionally separated into:

1. **state fixed points**: x = f(x);
2. **dynamic recurrence / periodicity**: f^n(x) = x;
3. **order-theoretic fixed points**: monotone endomaps on structured orders;
4. **diagonal / representational fixed points**: Lawvere-style self-application;
5. **computability fixed points**: Rogers/Kleene fixed points of program descriptions;
6. **logical translation bridges**: isomorphisms between distinction calculi and standard logical calculi.

The research question is which assumptions are necessary and sufficient to move between these classes.
