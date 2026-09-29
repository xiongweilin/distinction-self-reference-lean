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
| Weak representation | represent only the endomap-specific Lawvere diagonal | one represented diagonal already forces a fixed point; partial families can coexist when that diagonal is excluded |
| Semantic incompatibility | conditions interpreted on common realizations | fixed-point-free endomap and universal surjective representation form an explicit incompatible pair |
| Weak representation | represent only the endomap-specific diagonal function / selected family | the diagonal condition alone forces a fixed point; partial families can coexist with two-state crossing when the forbidden diagonal is absent |
| Future distinction | histories + continuation tests | histories are equivalent exactly when all future continuations agree; finite quotient iff regular by Myhill–Nerode |
| Bisimulation | observed transition system | persistent identity-as-behavior is a greatest fixed point with a coinduction principle |
| Labelled bisimulation bridge | canonical residual DFA + label preservation | future indistinguishability is exactly canonical labelled bisimilarity |
| Viability | actions + safe-state predicate | sustainable action region is the greatest fixed point of the safe-predecessor operator |
| Recovery | finite action plans + viability kernel | viable states are recoverable; a two-state model proves recoverable need not imply viable |
| Purpose-relative viability | bare dynamics + nontrivial acceptability direction | viability/recovery are monotone under purpose relaxation; identical dynamics can yield different kernels under different purposes |
| Purpose-relative capability | fixed dynamics + nontrivial acceptable-state distinction | changing only action-relevant direction can change the viability kernel; relaxing purpose is monotone for viability/recovery |
| Local/global | family of local constraints | even pairwise joint satisfiability need not imply a global witness |
| Nested gluing | finite nonempty linear order + nested constraints | local satisfiability already implies one global witness |
| Overlap gluing | local scopes + cover + agreement on overlaps | compatible local patches construct a global assignment; nesting is not required |
| Local sufficiency | observation + required commitment | sufficiency is factorization through the current observation; ambiguity witnesses certify insufficiency |
| Compositional sufficiency | locally sufficient observations + cover + overlap compatibility | local commitments glue into a global commitment decodable from combined observations |
| Conditional composition | compositional sufficiency + finite recoverability | constructs a global commitment witness together with a recovery plan back to viability |
| Local sufficiency | observation + commitment requirement | sufficiency is factorization of the required commitment through the current observation; ambiguity certifies insufficiency |
| Compositional sufficiency | local sufficiency + cover + overlap agreement | combined observations determine one global commitment extending every local requirement |
| Conditional composition | compositional sufficiency + recoverability | constructs a global commitment together with a finite recovery path to viability |
| Deterministic information order | representation + post-processing factorization | post-processing cannot create new distinctions; strict information loss exists |
| Markov garbling | experiment + Markov post-processing | Bayes risk cannot improve, risk-based information and KL divergence cannot increase |
| Information → future bridge | coarse summary factors through residual language | FutureEq histories remain equal under every such summary |
| Control abstraction | dynamics commute + safety preservation/reflection | preservation gives forward viability/recovery; reflection gives backward preservation; both give exact iff |
| Directional control simulation | possibly different action types + forward/backward step matching | forward simulation preserves capability forward; backward simulation reflects it back |
| Safety information sufficiency | abstraction fibers + safety label factorization | fiber-invariant safety iff the safety bit factors through the abstraction; exact capability follows with two-way simulation |
| Control condition ablation | remove one simulation/safety condition at a time | each of forward simulation, safety preservation, backward simulation, and safety reflection has an independent counterexample when omitted |
| Concrete control dependency graph | four control conditions + four directional capabilities | forward/backward condition pairs are inclusion-minimal; all four are minimal for all four capabilities |
| Meta-framework | monotone condition→capability graph + condition semantics | ablation minimality = inclusion minimality; compatibility/incompatibility, dominance, and capability equivalence are formalized |
| Concrete control dependency graph | four directional simulation/safety conditions | the proved two-condition pairs are inclusion-minimal for their viability/recovery capabilities |
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
- `DistinctionSelfReference/Purposeful.lean` — minimal action-relevant direction, purpose-relative viability/recovery monotonicity, and same-dynamics/different-purpose separation.
- `DistinctionSelfReference/Purposeful.lean` — action-relevant acceptable-state direction; purpose refinement is monotone for viability/recovery.
- `DistinctionSelfReference/LocalGlobal.lean` — local and pairwise-compatible counterexamples to global composition.
- `DistinctionSelfReference/NestedGluing.lean` — positive finite gluing theorem for nested constraint families.
- `DistinctionSelfReference/OverlapGluing.lean` — cover + overlap agreement gluing theorem, with a non-nested example.
- `DistinctionSelfReference/LocalSufficiency.lean` — observation-relative commitment sufficiency and ambiguity witnesses.
- `DistinctionSelfReference/CompositionalSufficiency.lean` — composition of locally sufficient commitments under cover and overlap agreement.
- `DistinctionSelfReference/ConditionalComposition.lean` — compositional commitment witness augmented with finite recovery to viability.
- `DistinctionSelfReference/LocalSufficiency.lean` — observation-relative commitment sufficiency and ambiguity obstruction.
- `DistinctionSelfReference/CompositionalSufficiency.lean` — local sufficiency + overlap gluing constructs a globally decodable commitment.
- `DistinctionSelfReference/ConditionalComposition.lean` — adds minimum recoverability to produce a conditional composition witness.
- `DistinctionSelfReference/FeasibleFramework.lean` — combines capability sufficiency with joint semantic realizability.
- `DistinctionSelfReference/Reopening.lean` — mismatch-triggered reopening, successful revision, false-alarm rejection, and exact correction.
- `DistinctionSelfReference/Corrigibility.lean` — bridges corrected revision to operational recovery and bisimulation-based self-continuity.
- `DistinctionSelfReference/CorrigibilityDependencyGraph.lean` — inclusion-minimal condition sets for four corrigibility capabilities.
- `DistinctionSelfReference/CorrigibilityAblation.lean` — finite countermodels for dropped reopening/recovery/continuity conditions plus a feasible minimal exact-correction framework.
- `DistinctionSelfReference/CapabilityOrder.lean` — capability profiles as a partial order and monotone capability chains.
- `DistinctionSelfReference/SelfModification.lean` — self-modification proposals, verifier soundness, invariant preservation, and non-degrading capability checks.
- `DistinctionSelfReference/VerifiedUpgrade.lean` — verified self-modification chains preserve invariants and capability monotonicity.
- `DistinctionSelfReference/IteratedReopening.lean` — repeated reality-facing revision, requirement tracking, and stabilization tracking.
- `DistinctionSelfReference/VerifierMigration.lean` — conservative verifier refinement and soundness propagation across verifier self-migration.
- `DistinctionSelfReference/GuardedRSI.lean` — composed guarded RSI loop combining self-modification, verifier migration, capability monotonicity, invariants, and reality tracking.
- `DistinctionSelfReference/RSIDependencyGraph.lean` — minimal condition sets for the first RSI capability graph.
- `DistinctionSelfReference/RSIAblation.lean` — countermodels for missing verifier soundness, capability non-degradation, verifier refinement, and reality detection.
- `DistinctionSelfReference/CertifiedVerifierExpansion.lean` — safe acceptance-domain expansion using an independently sound certificate authority, with a strict-expansion witness.
- `DistinctionSelfReference/CapabilityDynamics.lean` — strict capability growth, plateaus, modifier fixed points, and finite-universe cardinality bounds.
- `DistinctionSelfReference/VerificationResources.lean` — separates verifier acceptance from budget-bounded callability.
- `DistinctionSelfReference/LongRunRSI.lean` — discrete eventual-constancy notions for capability and reality convergence and their joint stabilization.
- `DistinctionSelfReference/AdvancedRSIDependencyGraph.lean` — minimal conditions for certified expansion, bounded callability, strict growth, and long-run stability.
- `DistinctionSelfReference/RSIFeasibility.lean` — concrete guarded-RSI realization proving the full first-layer condition set is feasible-inclusion-minimal.
- `DistinctionSelfReference/TrustedKernel.lean` — explicit proof objects, a small Boolean proof checker, kernel soundness, and sound verifier expansion through checked proofs.
- `DistinctionSelfReference/KernelVerificationResources.lean` — proof-dependent checking costs and budget-bounded callability for kernel-certified upgrades.
- `DistinctionSelfReference/FiniteCapabilityGrowth.lean` — global finite-universe bound on consecutive strict capability-growth steps.
- `DistinctionSelfReference/InformationOrder.lean` — deterministic refinement preorder and no-new-distinction theorem.
- `DistinctionSelfReference/MarkovGarbling.lean` — Markov post-processing order with Bayes-risk, risk-increase, and KL data-processing bridges.
- `DistinctionSelfReference/InformationFutureBridge.lean` — bridge from representation refinement to future indistinguishability.
- `DistinctionSelfReference/ControlAbstraction.lean` — exact conditions under which state abstraction preserves or reflects viability and recoverability, plus false-positive counterexamples.
- `DistinctionSelfReference/ControlSimulation.lean` — weaker directional simulations with possibly different action types; forward/backward conditions independently control capability preservation/reflection.
- `DistinctionSelfReference/SafetyInformation.lean` — safety sufficiency as fiber invariance / deterministic information factorization.
- `DistinctionSelfReference/ControlAblation.lean` — independent counterexamples showing the directional simulation and safety conditions cannot simply be dropped.
- `DistinctionSelfReference/ControlDependencyGraph.lean` — concrete minimal sufficient condition sets for the proved control capabilities.
- `DistinctionSelfReference/MetaFramework.lean` — condition/capability graphs plus semantic compatibility and incompatibility.
- `DistinctionSelfReference/OrderTheoretic.lean` — Mathlib / Knaster-Tarski bridge.
- `DistinctionSelfReference/Representational.lean` — Mathlib's type-level Lawvere fixed-point bridge.
- `DistinctionSelfReference/RepresentationalObstruction.lean` — fixed-point-free endomaps forbid Lawvere-style universal surjective representation.
- `DistinctionSelfReference/WeakRepresentation.lean` — per-endomap diagonal representability, family representation, and a partial two-state representation that coexists with fixed-point-free crossing.
- `DistinctionSelfReference/RepresentationConflict.lean` — semantic incompatibility instance for fixed-point-free endomaps versus universal representation.
- `DistinctionSelfReference/RepresentationConflict.lean` — instantiates the Lawvere obstruction as an upward-closed semantic incompatibility edge.
- `DistinctionSelfReference/WeakRepresentation.lean` — isolates per-endomap diagonal representability and exhibits partial representation compatible with two-state crossing.
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

## Next construction directions

This section is updated at the end of every completed construction phase.

Current next directions, in priority order:

1. **Full-version cycle / plateau diagnostics** — distinguish capability-profile plateaus from payload changes, version cycles, genuine modifier fixed points, and recurrent but non-improving self-modification.
2. **Indefinite resource-bounded callability** — characterize when an infinite or long upgrade sequence remains callable as proof sizes, checking costs, and available budgets change.
3. **Trusted-kernel migration** — allow the proof checker itself to change through predecessor-checked or dual-kernel handoff, while preserving an explicit trust invariant.
4. **Joint trust / capability / reality convergence** — compare stabilization of verifier trust, capability profiles, and reality-facing commitments, including bounded tracking lag rather than only exact eventual constancy.
5. **Advanced feasible-minimal RSI frameworks** — give semantic realizations and incompatibility edges for the new proof-kernel/resource conditions, not only dependency-graph minimality.

## Scope warning

The code in this repository is **not** initially a formalization of all of Spencer-Brown's *Laws of Form* or Varela's calculus. The RSI layer is likewise a guarded structural scaffold, not a claim of open-ended recursive self-improvement. Small models may be inspired by those ideas, but such relationships are stated explicitly and conservatively.

In particular, `InvolutiveDistinction` captures only a crossing-style involution. `PrimaryBoolean.Form` adds a small primary-shaped syntax and Boolean semantics, but it still does not formalize the full quotient/equational theory of Spencer-Brown's primary algebra. Likewise, `KleeneThree` formalizes the Strong Kleene semantic side, and `LogicBridge` only proves a semantic conservative-extension result on determined valuations. The full Varela syntax and Schwartz derivability-preserving isomorphism remain future targets.
