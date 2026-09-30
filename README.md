# Distinction / Self-Reference in Lean

A formal research project for studying which additional conditions turn a minimal distinction-and-reentry system into progressively stronger forms of self-reference.

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
| Local sufficiency | observation + required commitment | sufficiency is factorization through the observation and is equivalent to absence of an ambiguity witness |
| Compositional sufficiency | locally sufficient observations + cover + overlap compatibility | local commitments glue into a global commitment decodable from combined observations |
| Conditional composition | compositional sufficiency + finite recoverability | constructs a global commitment witness together with a recovery plan back to viability |
| Deterministic information order | representation + post-processing factorization | post-processing cannot create new distinctions; strict information loss exists |
| Markov garbling | experiment + Markov post-processing | Bayes risk cannot improve, risk-based information and KL divergence cannot increase |
| Information → future bridge | coarse summary factors through residual language | FutureEq histories remain equal under every such summary |
| Control abstraction | dynamics commute + safety preservation/reflection | preservation gives forward viability/recovery; reflection gives backward preservation; both give exact iff |
| Directional control simulation | possibly different action types + forward/backward step matching | forward simulation preserves capability forward; backward simulation reflects it back |
| Safety information sufficiency | abstraction fibers + safety label factorization | fiber-invariant safety iff the safety bit factors through the abstraction; exact capability follows with two-way simulation |
| Control condition ablation | remove one simulation/safety condition at a time | each of forward simulation, safety preservation, backward simulation, and safety reflection has an independent counterexample when omitted |
| Concrete control dependency graph | four control conditions + four directional capabilities | forward/backward condition pairs are inclusion-minimal; all four are minimal for all four capabilities |
| Meta-framework | monotone condition→capability graph + condition semantics | ablation minimality = inclusion minimality; compatibility/incompatibility, dominance, and capability equivalence are formalized |
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
| Changing evaluator | time-indexed local improvement relations | strict global extension exists iff the local-edge union is acyclic; on finite states this is equivalent to a Nat common potential |
| Evaluator grounding | fixed external goal + anchor + changing evaluator | sufficient anchor + semantic evaluator soundness + local improvement imply global goal improvement; insufficient finite anchors permit one-step and perpetual proxy regression |
| Evaluator provenance | versioned evaluator evidence + anchor evidence | history is retained while current qualification is selectively invalidated; full or goal-relevant preservation permits justified migration |
| Dynamic anchor grounding | delayed/reordered finite anchor observations | eventual freshness iff all eventually stable grounded Boolean judgments remain eventually aligned |
| Task-relative scheduling | one fixed eventually-stable task + source schedule | universal freshness implies task preservation, but a globally stale schedule can still preserve a specific nonconstant task |
| Stochastic anchor grounding | experiment + prior + decision loss + Markov garbling | Bayes-risk-zero grounding cannot be created by garbling; positive decision risk survives further information loss |
| Dependency-aware provenance | evidence dependency graph + versioned qualification | stale evaluator premises invalidate dependent conclusions transitively; stronger preservation policies monotonically restore evidence while independent anchor-supported conclusions survive |
| Branch/archive RSI | recurrent selected branch + retained archive | branch recurrence and branch-score plateau can coexist with strict archive growth; WQO makes antichain frontiers finite but does not itself imply archive stabilization |
| Partial Lawvere | Option-valued evaluator + diagonal representation | a represented partial diagonal forces a fixed point exactly when self-application is defined; fixed-point-free steps force the representing self-application to be undefined |
| Guarded Lawvere | explicit self-application guard + represented diagonal | an open self guard forces a fixed point; fixed-point-free steps force the self guard closed |
| Quantitative grounding | decision experiment + reference experiment + loss-scaled risk gap | exact grounding is the zero-gap case; risk-gap guarantees are monotone, compositional, and cannot be created by garbling |
| Task-family scheduling | stable task family + source schedule | family preservation has an exact criterion; universal stable Boolean tasks recover eventual freshness |
| Evaluator morphisms | evaluator/state map + proof-carrying preservation certificate | judgment/goal preservation composes and transports qualified evidence and dependencies across evaluator migration |
| Grounded archive dynamics | archive/frontier + evaluator + external goal + capability order | archive growth, frontier replacement, evaluator progress, grounded goal progress, and capability novelty are formally separated |
| Framework morphisms | condition/capability/realization maps + preservation laws | sufficiency and compatibility transport compositionally; reflection/equivalence control stronger invariants; certified images define invariant cores |
| guide dependency core | explicit guide dependency spine only | minimal self-reference, continuity, agency, effective finitude, purpose, local sufficiency, and corrigibility boundaries are formalized without collapsing reality to a finite state space |

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
- `DistinctionSelfReference/LocalGlobal.lean` — local and pairwise-compatible counterexamples to global composition.
- `DistinctionSelfReference/NestedGluing.lean` — positive finite gluing theorem for nested constraint families.
- `DistinctionSelfReference/OverlapGluing.lean` — cover + overlap agreement gluing theorem, with a non-nested example.
- `DistinctionSelfReference/LocalSufficiency.lean` — observation-relative commitment sufficiency and ambiguity witnesses.
- `DistinctionSelfReference/CompositionalSufficiency.lean` — composition of locally sufficient commitments under cover and overlap agreement.
- `DistinctionSelfReference/ConditionalComposition.lean` — compositional commitment witness augmented with finite recovery to viability.
- `DistinctionSelfReference/AnchorMinimality.lean` — least sufficient anchors, information-equivalence uniqueness, fiber characterization, and finite reachable-range cardinal lower bounds.
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
- `DistinctionSelfReference/ChangingEvaluator.lean` — exact acyclicity iff for strict global extensions; finite-state acyclicity iff Nat common potential; infinite-state counterexample separating the two.
- `DistinctionSelfReference/EvaluatorGrounding.lean` — semantic grounding through sufficient anchors, global external-goal improvement, finite-anchor regression, and a perpetual hidden proxy cycle.
- `DistinctionSelfReference/EvaluatorMorphism.lean` — first-class proof-carrying evaluator morphisms, goal/judgment preservation, identity/composition, and same-state version bridges.
- `DistinctionSelfReference/MorphismProvenance.lean` — bridge-induced provenance policy, evidence/dependency transport, composed-certificate examples, and morphism ablation countermodels.
- `DistinctionSelfReference/EvaluatorProvenance.lean` — evaluator-version provenance, selective current-evidence invalidation, exact/full preservation, and weaker goal-relevant evidence migration.
- `DistinctionSelfReference/DynamicAnchorGrounding.lean` — exact eventual-freshness criterion for delayed/reordered grounded Boolean judgments, plus stale-schedule counterexamples.
- `DistinctionSelfReference/TaskFamilyScheduling.lean` — exact family-relative schedule criterion, universal-family recovery of eventual freshness, and strict singleton-family separation.
- `DistinctionSelfReference/TaskRelativeScheduling.lean` — fixed-task preservation, universal-to-task implication, and a strict counterexample separating task adequacy from global eventual freshness.
- `DistinctionSelfReference/EvidenceDependency.lean` — dependency-aware current evidence, transitive stale-premise invalidation, selective survival of anchor-supported conclusions, and monotone revalidation under stronger preservation bridges.
- `DistinctionSelfReference/GroundedArchiveDynamics.lean` — separates archive growth, frontier replacement, evaluator-relative progress, fixed-goal grounded progress, capability novelty, evaluator migration, and two stopping criteria.
- `DistinctionSelfReference/ArchiveRSI.lean` — branch/archive separation, WQO stabilization for monotone antichains, dominance-complete Pareto frontiers, perpetual replacement under WQO, and the `WellFoundedGT` obstruction.
- `DistinctionSelfReference/PartialLawvere.lean` — partial diagonal representation and the defined-self-application threshold for Lawvere fixed points.
- `DistinctionSelfReference/GuardedLawvere.lean` — guard-separated diagonal representation; open self-application forces a fixed point and fixed-point-free maps force the self guard closed.
- `Research/FoundationBridge.md` — exact Foundation modules for Gödel I/II, Löb, and Tarski, with current Lean-toolchain integration constraint.
- `DistinctionSelfReference/NextRSIDependencyGraph.lean` — next-phase minimal condition sets for recurrence diagnostics, indefinite callability, kernel migration, and joint stabilization.
- `DistinctionSelfReference/NextRSIFeasibility.lean` — concrete semantic realizations proving all four next-phase condition sets feasible-inclusion-minimal.
- `DistinctionSelfReference/NextRSIConflict.lean` — semantic incompatibility of non-degrading full-version recurrence with strict capability growth inside the cycle.
- `DistinctionSelfReference/FiniteCapabilityGrowth.lean` — global finite-universe bound on consecutive strict capability-growth steps.
- `DistinctionSelfReference/InformationOrder.lean` — deterministic refinement preorder and no-new-distinction theorem.
- `DistinctionSelfReference/MarkovGarbling.lean` — Markov post-processing order with Bayes-risk, risk-increase, and KL data-processing bridges.
- `DistinctionSelfReference/StochasticAnchorGrounding.lean` — exact decision grounding as zero Bayes risk and its monotonicity under Markov garbling.
- `DistinctionSelfReference/QuantitativeGrounding.lean` — loss-scaled approximate grounding, risk-gap monotonicity, additive composition, and task-family bounds.
- `DistinctionSelfReference/QuantitativeGroundingExample.lean` — strict Boolean 0–1-loss example separating exact and approximate decision grounding.
- `DistinctionSelfReference/InformationFutureBridge.lean` — bridge from representation refinement to future indistinguishability.
- `DistinctionSelfReference/ControlAbstraction.lean` — exact conditions under which state abstraction preserves or reflects viability and recoverability, plus false-positive counterexamples.
- `DistinctionSelfReference/ControlSimulation.lean` — weaker directional simulations with possibly different action types; forward/backward conditions independently control capability preservation/reflection.
- `DistinctionSelfReference/SafetyInformation.lean` — safety sufficiency as fiber invariance / deterministic information factorization.
- `DistinctionSelfReference/ControlAblation.lean` — independent counterexamples showing the directional simulation and safety conditions cannot simply be dropped.
- `DistinctionSelfReference/ControlDependencyGraph.lean` — concrete minimal sufficient condition sets for the proved control capabilities.
- `DistinctionSelfReference/MetaFramework.lean` — condition/capability graphs plus semantic compatibility and incompatibility.
- `DistinctionSelfReference/FrameworkMorphism.lean` — compositional translations of conditions, capabilities, and realizations with derivation/satisfaction/compatibility transport, reflection criteria, and morphism-defined invariant cores.
- `DistinctionSelfReference/RSIFrameworkMorphisms.lean` — upgrades advanced/next RSI role translations into certified framework morphisms and recovers the legacy six-role core from morphism images.
- `DistinctionSelfReference/GuideCore.lean` — formalizes only the guide dependency spine with corrigibility as an independent branch, effective finitude separated from finite state spaces, and conditional composition backed by existing local-sufficiency/recoverability theorems.
- `DistinctionSelfReference/OrderTheoretic.lean` — Mathlib / Knaster-Tarski bridge.
- `DistinctionSelfReference/Representational.lean` — Mathlib's type-level Lawvere fixed-point bridge.
- `DistinctionSelfReference/RepresentationalObstruction.lean` — fixed-point-free endomaps forbid Lawvere-style universal surjective representation.
- `DistinctionSelfReference/WeakRepresentation.lean` — per-endomap diagonal representability, family representation, and a partial two-state representation that coexists with fixed-point-free crossing.
- `DistinctionSelfReference/RepresentationConflict.lean` — semantic incompatibility instance for fixed-point-free endomaps versus universal representation.
- `DistinctionSelfReference/Computability.lean` — Mathlib's Rogers/Kleene computability fixed-point bridge.
- `Research/Established.md` — established mathematical results and existing formalizations.
- `Research/Candidates.md` — proved-here propositions, targets, phase boundaries, and the meta-framework program.
- `Research/Roadmap.md` — closed convergence plan, deferred gates, and v1.0 dependency order.
- `Research/CoreTheoremIndex.md` — designated v1.0 public theorem cross-section with assumptions and boundary witnesses.
- `Research/FreezeChecklist.md` — pre-freeze verification status and stable-toolchain release gates.
- `DistinctionSelfReference/FreezeAudit.lean` — CI-only theorem-name and axiom audit for the designated v1.0 core; intentionally not imported by the library root.

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
