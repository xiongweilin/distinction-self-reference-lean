# Distinction / Self-Reference in Lean

A small formal research project for studying which additional conditions turn a minimal distinction-and-reentry system into progressively stronger forms of self-reference.

The project deliberately separates:

1. **Established results** from the literature and existing formalizations.
2. **Small executable/formal models** that isolate one condition at a time.
3. **Conjectures / research targets** that are not yet proved.

The first milestone starts from the weakest concrete crossing model we can test without pretending that it is the unique meaning of "distinction".

## Initial formal ladder

| Framework | Added conditions | Main result |
| --- | --- | --- |
| Core crossing | cross² = id | every state is a boundary fixed point or belongs to a nontrivial two-cycle |
| Finite crossing | finite carrier + involutive crossing | fixed-point-free carriers are even; odd carriers must contain a boundary fixed point |
| Two-state | exactly two states, both changed by cross | no static fixed point; the swap is the unique fixed-point-free endomap |
| Dynamic two-state | iteration of the swap | every orbit has exact period two rather than period one |
| Three-state | add one self-dual boundary state | exactly one static fixed point |
| Primary Boolean core | blank / juxtaposition / crossing / variables | exact raw-syntax translation to false/OR/NOT Boolean expressions, with semantics preserved |
| Strong Kleene core | three truth values + K3 connectives | three-state crossing transports to K3 negation; boundary/unknown is its unique fixed point |
| Boolean → K3 bridge | interpret primary-shaped forms in K3 | K3 conservatively extends Boolean valuations; `a ∨ ¬a` is true exactly when `a` is determined |
| Order-theoretic | complete lattice + monotone endomap | least and greatest fixed points exist by Knaster-Tarski |
| Representational | a surjective internal evaluator | every endomap of the represented result type has a fixed point (type-level Lawvere bridge) |
| Representational obstruction | fixed-point-free endomap on the result type | universal surjective self-representation is impossible; instantiated by the two-state crossing |
| Future distinction | histories + continuation tests | histories are equivalent exactly when all future continuations agree; finite quotient iff regular by Myhill–Nerode |
| Bisimulation | observed transition system | persistent identity-as-behavior is a greatest fixed point with a coinduction principle |
| Labelled bisimulation bridge | canonical residual DFA + label preservation | future indistinguishability is exactly canonical labelled bisimilarity |
| Viability | actions + safe-state predicate | sustainable action region is the greatest fixed point of the safe-predecessor operator |
| Recovery | finite action plans + viability kernel | viable states are recoverable; a two-state model proves recoverable need not imply viable |
| Local/global | family of local constraints | even pairwise joint satisfiability need not imply a global witness |
| Nested gluing | finite nonempty linear order + nested constraints | local satisfiability already implies one global witness |
| Overlap gluing | local scopes + cover + agreement on overlaps | compatible local patches construct a global assignment; nesting is not required |
| Deterministic information order | representation + post-processing factorization | post-processing cannot create new distinctions; strict information loss exists |
| Markov garbling | experiment + Markov post-processing | Bayes risk cannot improve, risk-based information and KL divergence cannot increase |
| Information → future bridge | coarse summary factors through residual language | FutureEq histories remain equal under every such summary |
| Control abstraction | dynamics commute + safety preservation/reflection | preservation gives forward viability/recovery; reflection gives backward preservation; both give exact iff |
| Directional control simulation | possibly different action types + forward/backward step matching | forward simulation preserves capability forward; backward simulation reflects it back |
| Safety information sufficiency | abstraction fibers + safety label factorization | fiber-invariant safety iff the safety bit factors through the abstraction; exact capability follows with two-way simulation |
| Control condition ablation | remove one simulation/safety condition at a time | each of forward simulation, safety preservation, backward simulation, and safety reflection has an independent counterexample when omitted |
| Meta-framework | monotone condition→capability graph | one-condition ablation minimality is equivalent to inclusion-minimal sufficiency; capability dominance/equivalence are formalized |
| Computability | program codes + evaluator + computability | Rogers fixed point and Kleene's second recursion theorem |

This is intentionally a branching ladder: static, dynamic, order-theoretic, diagonal, and computability forms of self-reference should not be identified without a proof relating them.

## Repository layout

- `DistinctionSelfReference/Core.lean` — weak interfaces for crossing and re-entry; fixed-point/two-cycle classification.
- `DistinctionSelfReference/Finite.lean` — parity consequence for finite fixed-point-free crossing.
- `DistinctionSelfReference/TwoState.lean` — minimal binary crossing.
- `DistinctionSelfReference/Dynamic.lean` — dynamic period-two re-entry.
- `DistinctionSelfReference/ThreeState.lean` — one self-dual boundary state.
- `DistinctionSelfReference/PrimaryBoolean.lean` — Boolean semantic core for primary-shaped forms.
- `DistinctionSelfReference/KleeneThree.lean` — Strong Kleene three-valued semantics and three-state crossing bridge.
- `DistinctionSelfReference/LogicBridge.lean` — conservative Boolean-to-K3 interpretation and the exact excluded-middle boundary.
- `DistinctionSelfReference/FutureDistinction.lean` — future-indistinguishability and the Myhill–Nerode bridge.
- `DistinctionSelfReference/Bisimulation.lean` — persistent behavioral identity as a greatest fixed point.
- `DistinctionSelfReference/LabeledBisimulation.lean` — label-preserving greatest-fixed-point bisimulation.
- `DistinctionSelfReference/FutureBisimulation.lean` — exact bridge between future equivalence and canonical labelled bisimilarity.
- `DistinctionSelfReference/Viability.lean` — controlled viability kernel as a greatest fixed point.
- `DistinctionSelfReference/Recovery.lean` — finite-plan recoverability back to the viability kernel.
- `DistinctionSelfReference/RecoverySeparation.lean` — minimal model proving recoverable does not imply viable.
- `DistinctionSelfReference/LocalGlobal.lean` — local and pairwise-compatible counterexamples to global composition.
- `DistinctionSelfReference/NestedGluing.lean` — positive finite gluing theorem for nested constraint families.
- `DistinctionSelfReference/OverlapGluing.lean` — cover + overlap agreement gluing theorem, with a non-nested example.
- `DistinctionSelfReference/InformationOrder.lean` — deterministic refinement preorder and no-new-distinction theorem.
- `DistinctionSelfReference/MarkovGarbling.lean` — Markov post-processing order with Bayes-risk, risk-increase, and KL data-processing bridges.
- `DistinctionSelfReference/InformationFutureBridge.lean` — bridge from representation refinement to future indistinguishability.
- `DistinctionSelfReference/ControlAbstraction.lean` — exact conditions under which state abstraction preserves or reflects viability and recoverability, plus false-positive counterexamples.
- `DistinctionSelfReference/ControlSimulation.lean` — weaker directional simulations with possibly different action types; forward/backward conditions independently control capability preservation/reflection.
- `DistinctionSelfReference/SafetyInformation.lean` — safety sufficiency as fiber invariance / deterministic information factorization.
- `DistinctionSelfReference/ControlAblation.lean` — independent counterexamples showing the directional simulation and safety conditions cannot simply be dropped.
- `DistinctionSelfReference/MetaFramework.lean` — monotone condition/capability graphs, sufficient target sets, ablation minimality, inclusion minimality, dominance, and capability equivalence.
- `DistinctionSelfReference/OrderTheoretic.lean` — Mathlib / Knaster-Tarski bridge.
- `DistinctionSelfReference/Representational.lean` — Mathlib's type-level Lawvere fixed-point bridge.
- `DistinctionSelfReference/RepresentationalObstruction.lean` — fixed-point-free endomaps forbid Lawvere-style universal surjective representation.
- `DistinctionSelfReference/Computability.lean` — Mathlib's Rogers/Kleene computability fixed-point bridge.
- `Research/Established.md` — established mathematical results and existing formalizations.
- `Research/Candidates.md` — proved-here propositions, next targets, and the meta-framework program.

## Initial questions

- What is the weakest structure needed to represent a distinction?
- When does re-entry mean a static fixed point, and when is it better represented dynamically?
- Which extra conditions force fixed points?
- Which extra conditions create new states rather than contradictions?
- Can different self-reference frameworks be compared by implication / interpretation?
- Is there a useful notion of a minimal sufficient self-reference meta-framework?

## Scope warning

The code in this repository is **not** initially a formalization of all of Spencer-Brown's *Laws of Form* or Varela's calculus. Small models may be inspired by those ideas, but such relationships are stated explicitly and conservatively.

In particular, `InvolutiveDistinction` captures only a crossing-style involution. `PrimaryBoolean.Form` adds a small primary-shaped syntax and Boolean semantics, but it still does not formalize the full quotient/equational theory of Spencer-Brown's primary algebra. Likewise, `KleeneThree` formalizes the Strong Kleene semantic side, and `LogicBridge` only proves a semantic conservative-extension result on determined valuations. The full Varela syntax and Schwartz derivability-preserving isomorphism remain future targets.
