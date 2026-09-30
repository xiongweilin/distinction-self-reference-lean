# Convergence roadmap

[English](Roadmap.md) | [简体中文](./Roadmap.zh-CN.md)

This document narrows the remaining large research program into a finite sequence
of phases. Each phase should be a separate PR and should close before the next
dependent phase begins.

## PR #4 — Quantitative Grounding

Status: **merged.**

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

Implemented additions also include a uniform bounded-loss risk surrogate and a concrete Boolean 0–1-loss strict garbling example.

## PR #5 — Evaluator Morphisms & Proof-Carrying Provenance

Status: **merged.**

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

The existing RQGM-style selective-erasure pattern is now captured structurally: evaluator-dependent evidence is invalidated without a bridge; independent anchor evidence survives; certified preserved evidence and covered dependency chains migrate. The phase also includes an ablation countermodel showing that preserving the external goal without preserving evaluator judgments is insufficient.

## PR #6 — Self-Certification / Löb Boundary

Status: **blocked by toolchain alignment; tracked as issue #6.**

Goal: replace the current abstract Löb interface by concrete formal-logic
instances: reflection, Löb, Gödel II, and Tarski boundaries.

Hard prerequisite: compatible Lean / Mathlib pins with
`FormalizedFormalLogic/Foundation`.

Do not weaken the trust boundary merely to make the dependency compile.

## PR #7 — Grounded Branching & Archive Dynamics

Status: **merged.**

Goal: combine the archive, changing-evaluator, and grounding lines.

Keep the following distinctions explicit:

- archive-cardinality growth;
- Pareto/frontier replacement;
- evaluator-relative improvement;
- externally grounded improvement;
- genuinely novel capability.

Implemented targets include evaluator migration and evidence validity; explicit separation of archive growth, frontier replacement, evaluator-relative progress, externally grounded progress, and capability novelty; morphism transport of frontier progress; and two sharper stopping criteria: a `WellFoundedGT` capability order under capability-sound evaluators, or a uniformly bounded fixed external goal under goal-sound evaluators. Do not treat archive growth alone as capability progress.

## PR #8 — Typed / Modal / Computational Self-Reference

Status: **deferred beyond v1.0; draft closed without merge.**

Goal: deepen the Lawvere / Kleene branch only where typing, partiality,
modality, or effects sharpen the self-application threshold.

Promising axes:

- typed partial evaluators;
- later / guarded modality;
- effectful or partial self-application;
- bridge to computability / Kleene recursion.

The draft did not establish a genuinely sharper diagonal threshold or a new
computability bridge, so it is deliberately excluded from the frozen v1.0 scope
rather than merged for roadmap completeness.

## PR #9 — Framework Morphisms + guide Core

Status: **merged.**

Goal: replace manually supplied role maps by general structure-preserving
translations between frameworks.

Implemented interface:

- condition, capability, and realization maps;
- derivability and condition-satisfaction preservation;
- compatibility preservation derived from realization transport;
- identity and composition;
- sufficiency and feasible-sufficiency transport;
- explicit derivation reflection for dominance/equivalence transport;
- a necessity countermodel showing preservation alone is insufficient;
- invariant condition cores induced by certified morphism images.

Only the mathematically explicit dependency spine from `xiongweilin/guide`
should be formalized. In particular:

- effective finitude must not be collapsed to `Fintype State`;
- reality must not be represented as an exhaustively enumerable total state;
- corrigibility remains a separable strengthening branch.

Implemented guide spine (with technical coverage bundled inside local-sufficiency evidence rather than promoted to a new philosophical primitive):

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

Status: **PR #10 merged; repository content is pre-v1.0 frozen. The final v1.0 tag remains blocked on a stable Lean 4.35+ toolchain pin.**

Goal: turn the research history into a stable proof artifact.

No additional theory PR is mandatory before v1.0. The remaining mandatory work is release-toolchain stabilization and replay.

Target acceptance:

- stable Lean / Mathlib release pins;
- `lake build`;
- `lake check`;
- the full `lake check --paranoid` checker set; in GitHub CI this is decomposed across independent jobs over one exact export because hosted runners enforce a shorter per-job lifetime than the combined checker sequence;
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

PR #8 typed/modal self-reference is deferred outside the mandatory v1.0 scope.
```

## External-theory positioning

- Blackwell–Le Cam theory motivates PR #4: deficiency quantifies experiment
  approximation by uniform decision-risk degradation. The current Lean layer
  formalizes the risk-bound side first.
- Proof-carrying-code ideas motivate explicit, independently checkable bridge
  certificates in PR #5, but the evaluator-morphism API is project-specific.
- Guarded recursion / later modalities motivated PR #8, but the draft was
  closed because standard guarded fixed-point results alone were not a sufficient
  project contribution.
- Institution morphisms / comorphisms provide an established analogue for PR #9:
  translations between logical systems should preserve an explicit satisfaction
  or derivability structure.
