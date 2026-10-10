# Distinction / Self-Reference in Lean

[English](README.md) | [简体中文](./README.zh-CN.md)

A formal research project for studying which additional conditions turn a minimal distinction-and-reentry system into progressively stronger forms of self-reference.

The project deliberately separates:

1. **Established results** from the literature and existing formalizations.
2. **Small executable/formal models** that isolate one condition at a time.
3. **Conjectures / research targets** that are not yet proved.

The first milestone starts from the weakest concrete crossing model we can test without pretending that it is the unique meaning of "distinction".

## Verified scope at a glance

This project proves conditional mathematical statements, not an ontology of mind, an empirical claim about AI, or the unconditional safety of recursive self-improvement. The minimal externally inspectable claims are:

- **Involutions:** a crossing state is fixed or belongs to a two-cycle; finite odd carriers have a fixed point.
- **Representation:** the Lawvere-style fixed-point obstruction requires a representability/diagonal assumption. A mere two-state swap does not prove general self-reference.
- **Judgment:** observation-relative commitment sufficiency means factorization through an observation; it is **not** guide's real-world three-way judgment or its causal benefit.
- **Composition:** local statements compose only with the specified coverage, overlap-compatibility, and where applicable recovery assumptions.
- **RSI/evaluators:** soundness or improvement transfers only under named trust, anchor, goal-preservation, and resource/freshness assumptions. Those assumptions are not guaranteed by the theorem itself.

The authoritative auditable cross-section is [the v1.0 core theorem index](Research/CoreTheoremIndex.md), checked in [`FreezeAudit.lean`](DistinctionSelfReference/FreezeAudit.lean). For research branches and countermodels, see [Candidates](Research/Candidates.md). The complete compiled module inventory is the import list in [`DistinctionSelfReference.lean`](DistinctionSelfReference.lean). The [freeze checklist](Research/FreezeChecklist.md) records precisely what is and is not ready for release.

## Initial questions

- What is the weakest structure needed to represent a distinction?
- When does re-entry mean a static fixed point, and when is it better represented dynamically?
- Which extra conditions force fixed points?
- Which extra conditions create new states rather than contradictions?
- Can different self-reference frameworks be compared by implication / interpretation?
- Is there a useful notion of a minimal sufficient self-reference meta-framework?

## RSI phase summary

The RSI line has now moved beyond a single monotone-upgrade model into a family of formally separated dimensions:

- **Self-modification and invariant preservation** — verified upgrades, verifier migration, trusted-kernel handoff, proof-checked expansion, and compromise-aware delegation are formalized separately.
- **Capability order and long-run dynamics** — strict growth, plateaus, recurrence, full-version cycles, finite growth bounds, infinite strict chains, and well-founded-rank obstructions are distinguished.
- **Reality verification** — exact correction, fixed/variable delay, reordered observations, eventual freshness, and an iff criterion for preservation of all eventually stable Boolean requirements are proved.
- **Evaluator grounding** — an external signal is distinguished from a sufficient external anchor; local evaluator improvement is meaningful only through a semantic factorization to one fixed external goal, and evaluator-version provenance is tracked independently of historical retention.
- **Verification resources** — certification is separated from callability; exogenous budgets, endogenous consumption/regeneration, indefinite callability, and a resource viability kernel are formalized.
- **Trust and certification** — predecessor migration, dual overlap, quorum delegation, compromise recovery, and translated trust-role invariant cores are present, but they still assume some non-circular soundness premise.
- **Meta-framework comparison** — feasible-minimal condition sets, incompatibility edges, semantic role translations, and a six-role RSI invariant core have been constructed.

The current frontier is therefore no longer “can a monotone RSI chain grow?” but **when improvement remains meaningful as the evaluator, verifier, branch structure, and resource state themselves change**.

## Freeze status

The planned convergence phases are content-complete:

- PR #4 — **Quantitative Grounding**: merged.
- PR #5 — **Evaluator Morphisms & Proof-Carrying Provenance**: merged.
- PR #7 — **Grounded Branching & Archive Dynamics**: merged.
- PR #9 — **Framework Morphisms + guide Core**: merged.
- PR #10 — **v1.0 pre-freeze proof hardening**: merged.

The repository is therefore **content-complete / pre-v1.0 frozen**. New theory is
not part of the mandatory v1.0 scope. The remaining release gate is external:
select and pin a stable Lean 4.35+ / compatible Mathlib toolchain, replay the
freeze checks on that exact pin, then tag v1.0.

Two research items remain explicitly outside the mandatory freeze:

- issue #6 keeps the concrete Foundation/Löb/Gödel/Tarski integration blocked
  until the toolchains align without weakening trust assumptions;
- typed/modal/computational self-reference is deferred beyond v1.0 because the
  draft did not establish a sharper self-application threshold than the existing
  partial/guarded Lawvere layer.

See `Research/Roadmap.md`, `Research/CoreTheoremIndex.md`, and
`Research/FreezeChecklist.md` for the maintained freeze boundary and release
criteria.

## Scope warning

The code in this repository is **not** initially a formalization of all of Spencer-Brown's *Laws of Form* or Varela's calculus. The RSI layer is likewise a guarded structural scaffold, not a claim of open-ended recursive self-improvement. Small models may be inspired by those ideas, but such relationships are stated explicitly and conservatively.

In particular, `InvolutiveDistinction` captures only a crossing-style involution. `PrimaryBoolean.Form` adds a small primary-shaped syntax and Boolean semantics, but it still does not formalize the full quotient/equational theory of Spencer-Brown's primary algebra. Likewise, `KleeneThree` formalizes the Strong Kleene semantic side, and `LogicBridge` only proves a semantic conservative-extension result on determined valuations. The full Varela syntax and Schwartz derivability-preserving isomorphism remain outside the frozen v1.0 scope.
