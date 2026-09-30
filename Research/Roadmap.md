# Convergence roadmap

This document narrows the remaining large research program into a finite sequence
of phases. Each phase should be a separate PR and should close before the next
dependent phase begins.

## PR #4 — Quantitative Grounding

Goal: move from exact sufficiency / zero Bayes risk to quantitative,
decision-relative approximate sufficiency.

Core targets:

- loss-scaled excess Bayes-risk / regret bounds;
- monotonicity under Markov post-processing;
- additive/compositional error bounds;
- an exact task-family scheduling criterion;
- at least one strict separation / countermodel.

Current implementation deliberately starts from the **risk side** of the
Blackwell–Le Cam randomization viewpoint. It does not yet claim that a
total-variation Le Cam deficiency or the full randomization theorem is
formalized in Mathlib.

Acceptance:

- epsilon = 0 recovers the exact grounding boundary;
- family risk-gap bounds compose;
- post-processing cannot create a risk-gap guarantee;
- family scheduling has an iff criterion and a strict example;
- final PR head passes `lake build`.

## PR #5 — Evaluator Morphisms & Proof-Carrying Provenance

Goal: replace edge-by-edge evaluator preservation predicates by a compositional
structure.

Expected interface:

- evaluator morphism;
- identity and composition;
- goal preservation;
- explicit bridge / preservation certificate;
- evidence and dependency transport;
- certificate composition;
- countermodel showing that an invalid morphism can transport an invalid
  conclusion.

The existing RQGM-style selective-erasure pattern should be treated as an
application: evaluator-dependent evidence is invalidated without a bridge;
independent anchor evidence survives; certified preserved evidence may migrate.

## PR #6 — Self-Certification / Loeb Boundary

Goal: replace the current abstract Loeb interface by concrete formal-logic
instances: reflection, Loeb, Goedel II, and Tarski boundaries.

Hard prerequisite: compatible Lean / Mathlib pins with
`FormalizedFormalLogic/Foundation`.

Do not weaken the trust boundary merely to make the dependency compile.

## PR #7 — Grounded Branching & Archive Dynamics

Goal: combine the archive, changing-evaluator, and grounding lines.

Keep the following distinctions explicit:

- archive-cardinality growth;
- Pareto/frontier replacement;
- evaluator-relative improvement;
- externally grounded improvement;
- genuinely novel capability.

Targets should include evaluator migration and evidence validity, plus sharper
WQO / chain-condition criteria. Do not treat archive growth alone as capability
progress.

## PR #8 — Typed / Modal / Computational Self-Reference

Goal: deepen the Lawvere / Kleene branch only where typing, partiality,
modality, or effects sharpen the self-application threshold.

Promising axes:

- typed partial evaluators;
- later / guarded modality;
- effectful or partial self-application;
- bridge to computability / Kleene recursion.

This phase is parallelizable and is not a hard prerequisite for v1.0 unless it
produces a genuinely sharper diagonal threshold.

## PR #9 — Framework Morphisms + guide Core

Goal: replace manually supplied role maps by general structure-preserving
translations between frameworks.

Expected interface:

- condition map;
- capability map;
- derivability preservation;
- compatibility / realizability preservation;
- identity and composition;
- framework equivalence / dominance preservation;
- invariant cores induced by allowed morphisms.

Only the mathematically explicit dependency spine from `xiongweilin/guide`
should be formalized. In particular:

- effective finitude must not be collapsed to `Fintype State`;
- reality must not be represented as an exhaustively enumerable total state;
- corrigibility remains a separable strengthening branch.

Candidate spine:

```
minimal self-reference
+ continuity
+ agency
+ effective finitude
+ purpose
-> local sufficiency problem

corrigibility = independent strengthening branch

local sufficiency
+ compatibility
+ recoverability
-> conditional composition
```

## v1.0 Freeze

Goal: turn the research history into a stable proof artifact.

Target acceptance:

- stable Lean / Mathlib release pins;
- `lake build`;
- `lake check`;
- `lake check --paranoid`;
- no `sorry`;
- no undeclared / unexpected axioms;
- assumptions indexed for core theorems;
- every necessity claim paired with a countermodel;
- Established / Proved here / Conjecture kept strictly separate;
- stable public API and explicit scope freeze.

## Dependency order

```
PR #3 evaluator grounding
  |
PR #4 quantitative / task-family grounding
  |
PR #5 evaluator morphisms
  |\
  | +----> PR #6 Loeb / Foundation, after toolchain alignment
  |
PR #7 grounded archive dynamics
  |
PR #9 framework morphisms / guide core
  |
v1.0 freeze

PR #8 typed/modal self-reference can proceed independently.
```

## External-theory positioning

- Blackwell–Le Cam theory motivates PR #4: deficiency quantifies experiment
  approximation by uniform decision-risk degradation. The current Lean layer
  formalizes the risk-bound side first.
- Proof-carrying-code ideas motivate explicit, independently checkable bridge
  certificates in PR #5, but the evaluator-morphism API is project-specific.
- Guarded recursion / later modalities motivate PR #8, but standard guarded
  fixed-point results alone are not sufficient project contributions.
- Institution morphisms / comorphisms provide an established analogue for PR #9:
  translations between logical systems should preserve an explicit satisfaction
  or derivability structure.
