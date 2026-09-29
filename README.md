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
| Full-version recurrence diagnostics | non-degrading self-modifier + complete version identity | recurrent version segments are capability plateaus; payload/version cycles need not be modifier fixed points |
| Indefinite proof-bounded callability | proposal stream + proof costs + time-indexed budgets | uniform bounded witnesses and covering budgets imply callability forever; certification alone need not imply eventual callability |
| Trusted-kernel migration | explicit checker versions + predecessor-checked handoff proofs | initial trust propagates along migration and every migrated proposal kernel remains invariant-sound |
| Joint RSI convergence | capability/trust/reality sequences + fixed tracking lag | eventual stabilization composes across all three axes; fixed-lag reality tracking preserves convergence in the shifted frame |
| Next-phase feasible RSI graph | semantic realizations + incompatibility edges | four new condition sets are feasible-inclusion-minimal; non-degradation + recurrence + strict first-step capability growth is incompatible |
| Variable-delay reality verification | arbitrary source schedule + eventual freshness | eventual requirement stability transfers through variable/out-of-order delay; permanent staleness gives a counterexample |
| Endogenous verification resources | evolving budget + checking cost + regeneration | bounded costs with self-sustaining regeneration imply indefinite callability; certification alone does not prevent resource exhaustion |
| Dual trust delegation | compromise predicate + overlapping approvals | one healthy overlapping checker is sufficient to transfer soundness after another checker is compromised; trust expansion and revocation are explicit |
| Infinite capability order | chain condition versus infinite capability universe | finite universes forbid everywhere-strict infinite growth, while a canonical Nat-capability chain grows strictly forever |
| First RSI invariant core | translations from three trust architectures into shared semantic roles | trust anchor + soundness transfer form the common translated core; validation evidence is architecture-specific |
| Exact scheduling criterion | variable/reordered source schedule | eventual freshness iff every eventually stable Boolean requirement remains eventually stable when sampled through the schedule |
| Resource viability bridge | controlled budget state + cost + regeneration actions | sustainable verification budgets are exactly a viability kernel; a no-regeneration unit-cost system has empty kernel |
| Threshold trust delegation | finite approving quorum + compromise bound | quorum size at least k and fewer than k compromised approvers force a healthy approver and sound successor; quorum count alone is insufficient |
| Ranked capability growth | strict-growth-reflecting rank into a WellFoundedGT order | such a rank rules out infinite strict capability growth; open-ended Nat capability growth forbids every such rank |
| Full RSI invariant-role core | two distinct RSI condition languages + semantic role translation | both cover self-modification, capability order, invariant preservation, reality verification, trust transfer, and resource callability |
| Self-certification barrier | internal certification + semantic soundness + abstract Löb rule | universal self-certification can be semantically unsound; internal reflection collapses to proof under Löb; a grounded root restores sound transfer |
| Changing evaluator | time-indexed local improvement relations | coherent embedding into one transitive global relation composes local improvements; arbitrary changing evaluators can rationalize a recurrent path |
| Branch/archive RSI | recurrent selected branch + retained archive | branch recurrence and branch-score plateau can coexist with strict archive growth; WQO makes antichain frontiers finite but does not itself imply archive stabilization |
| Partial Lawvere | Option-valued evaluator + diagonal representation | a represented partial diagonal forces a fixed point exactly when self-application is defined; fixed-point-free steps force the representing self-application to be undefined |

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
- `DistinctionSelfReference/FullVersionDiagnostics.lean` — distinguishes profile plateaus, full-version recurrence, two-cycles, and genuine modifier fixed points; proves recurrent non-degrading cycles contain no strict capability growth.
- `DistinctionSelfReference/VerificationResources.lean` — separates verifier acceptance from budget-bounded callability.
- `DistinctionSelfReference/LongRunRSI.lean` — discrete eventual-constancy notions for capability and reality convergence and their joint stabilization.
- `DistinctionSelfReference/AdvancedRSIDependencyGraph.lean` — minimal conditions for certified expansion, bounded callability, strict growth, and long-run stability.
- `DistinctionSelfReference/RSIFeasibility.lean` — concrete guarded-RSI realization proving the full first-layer condition set is feasible-inclusion-minimal.
- `DistinctionSelfReference/TrustedKernel.lean` — explicit proof objects, a small Boolean proof checker, kernel soundness, and sound verifier expansion through checked proofs.
- `DistinctionSelfReference/KernelVerificationResources.lean` — proof-dependent checking costs and budget-bounded callability for kernel-certified upgrades.
- `DistinctionSelfReference/IndefiniteCallability.lean` — infinite/eventual proposal-stream callability under changing budgets, including a certified-but-never-callable countermodel.
- `DistinctionSelfReference/TrustedKernelMigration.lean` — predecessor-checked proof-kernel handoff with explicit trust-invariant and soundness propagation.
- `DistinctionSelfReference/JointRSIConvergence.lean` — fixed-lag reality tracking and joint trust-version/capability/reality stabilization.
- `DistinctionSelfReference/VariableDelayReality.lean` — eventual-freshness criterion for variable/reordered reality observations, with a permanently stale counterexample.
- `DistinctionSelfReference/EndogenousResources.lean` — budget consumption/regeneration dynamics and a sustainable-callability theorem plus depletion counterexample.
- `DistinctionSelfReference/TrustDelegation.lean` — compromise-aware dual-checker delegation, recovery through one healthy overlap, and explicit trust expansion/revocation.
- `DistinctionSelfReference/InfiniteCapabilityOrder.lean` — finite no-infinite-growth theorem, canonical open-ended Nat capability chain, and abstract ascending-chain condition.
- `DistinctionSelfReference/RSIInvariantCore.lean` — first M5-style cross-framework role translation and trust invariant-core extraction.
- `DistinctionSelfReference/SchedulingCriterion.lean` — exact equivalence between eventual freshness and preservation of all eventually stable Boolean reality requirements.
- `DistinctionSelfReference/ResourceViability.lean` — verification-resource dynamics as a controlled viability problem, including sustainable floor theorem and empty-kernel depletion example.
- `DistinctionSelfReference/ThresholdTrust.lean` — quorum handoff under bounded compromise plus an all-compromised-quorum counterexample.
- `DistinctionSelfReference/RankedCapability.lean` — well-founded rank certificates that exclude open-ended strict capability growth.
- `DistinctionSelfReference/FullRSIInvariantCore.lean` — six-role full-RSI semantic core across two distinct condition languages.
- `DistinctionSelfReference/SelfCertificationBarrier.lean` — circular-certification countermodel, semantic transfer with an external anchor, and an abstract Löb reflection barrier.
- `DistinctionSelfReference/ChangingEvaluator.lean` — local-to-global coherence theorem, common-potential interface, and recurrent locally-improving counterexample.
- `DistinctionSelfReference/ArchiveRSI.lean` — branch recurrence versus archive growth plus Mathlib WQO/finite-antichain bridge.
- `DistinctionSelfReference/PartialLawvere.lean` — partial diagonal representation and the defined-self-application threshold for Lawvere fixed points.
- `Research/FoundationBridge.md` — exact Foundation modules for Gödel I/II, Löb, and Tarski, with current Lean-toolchain integration constraint.
- `DistinctionSelfReference/NextRSIDependencyGraph.lean` — next-phase minimal condition sets for recurrence diagnostics, indefinite callability, kernel migration, and joint stabilization.
- `DistinctionSelfReference/NextRSIFeasibility.lean` — concrete semantic realizations proving all four next-phase condition sets feasible-inclusion-minimal.
- `DistinctionSelfReference/NextRSIConflict.lean` — semantic incompatibility of non-degrading full-version recurrence with strict capability growth inside the cycle.
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

## RSI phase summary

The RSI line has now moved beyond a single monotone-upgrade model into a family of formally separated dimensions:

- **Self-modification and invariant preservation** — verified upgrades, verifier migration, trusted-kernel handoff, proof-checked expansion, and compromise-aware delegation are formalized separately.
- **Capability order and long-run dynamics** — strict growth, plateaus, recurrence, full-version cycles, finite growth bounds, infinite strict chains, and well-founded-rank obstructions are distinguished.
- **Reality verification** — exact correction, fixed/variable delay, reordered observations, eventual freshness, and an iff criterion for preservation of all eventually stable Boolean requirements are proved.
- **Verification resources** — certification is separated from callability; exogenous budgets, endogenous consumption/regeneration, indefinite callability, and a resource viability kernel are formalized.
- **Trust and certification** — predecessor migration, dual overlap, quorum delegation, compromise recovery, and translated trust-role invariant cores are present, but they still assume some non-circular soundness premise.
- **Meta-framework comparison** — feasible-minimal condition sets, incompatibility edges, semantic role translations, and a six-role RSI invariant core have been constructed.

The current frontier is therefore no longer “can a monotone RSI chain grow?” but **when improvement remains meaningful as the evaluator, verifier, branch structure, and resource state themselves change**.

## Next construction directions

This section is updated at the end of every completed construction phase.

Current deep-frontier priorities, in order:

1. **Self-modifying verifier without an independent trust anchor** — instantiate the current abstract Löb interface with `FormalizedFormalLogic/Foundation` once the Lean/Mathlib pins align, then characterize exactly which self-certification / verifier-migration interfaces imply an internal reflection principle. Connect those interfaces to Löb, Gödel II, and Tarski rather than treating verifier soundness as an external invariant by default. The key target is an iff-style boundary between circular/vacuous certification and migration justified by a genuinely non-circular grounding.

2. **Changing evaluator: local improvement → global improvement** — strengthen the current common-global-relation theorem toward a necessary-and-sufficient characterization. Candidate formulations include acyclicity of the union of local improvement edges, existence of a common potential, coherent order embeddings between evaluator versions, and minimal finite counterexamples showing that local improvement can cycle when evaluator migration is unconstrained.

3. **Archive / branching RSI** — replace the single linear version chain by a branching version graph and a retained Pareto/archive object. Formalize exact relations among branch growth, branch recurrence, individual plateau, archive dominance growth, archive recurrence, and archive plateau. Use Mathlib's WQO/antichain machinery to determine which capability orders force finite Pareto frontiers and which still permit indefinite archive progress.

4. **Partial / guarded Lawvere self-reference** — extend the proved Option-valued threshold from plain partiality to typed evaluators, guarded/later modalities, and effectful computation. The main question is the exact representational threshold at which diagonal self-application becomes defined strongly enough to force a fixed point.

5. **Resources remain a feasibility dimension** — keep `IndefiniteCallability`, endogenous resources, and resource viability as constraints on the four theories above. Finite capability universes and finite strict-growth bounds remain useful baseline models, not the main frontier.

## Scope warning

The code in this repository is **not** initially a formalization of all of Spencer-Brown's *Laws of Form* or Varela's calculus. The RSI layer is likewise a guarded structural scaffold, not a claim of open-ended recursive self-improvement. Small models may be inspired by those ideas, but such relationships are stated explicitly and conservatively.

In particular, `InvolutiveDistinction` captures only a crossing-style involution. `PrimaryBoolean.Form` adds a small primary-shaped syntax and Boolean semantics, but it still does not formalize the full quotient/equational theory of Spencer-Brown's primary algebra. Likewise, `KleeneThree` formalizes the Strong Kleene semantic side, and `LogicBridge` only proves a semantic conservative-extension result on determined valuations. The full Varela syntax and Schwartz derivability-preserving isomorphism remain future targets.
