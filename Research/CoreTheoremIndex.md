# v1.0 core theorem index

This file defines the **v1.0 core** for stability and assumption review. It is
not a claim that every theorem outside this list is secondary mathematics; it is
the public cross-section whose names, scopes, and assumptions are expected to
remain stable across the freeze.

The machine-readable companion is
`DistinctionSelfReference/FreezeAudit.lean`, which CI elaborates separately and
prints kernel axioms for every theorem listed here.

| Area | Core theorem | Explicit assumptions / scope | Necessity or boundary witness |
| --- | --- | --- | --- |
| Minimal distinction | `InvolutiveDistinction.boundary_or_twoCycle` | one involutive crossing operation | two-state fixed-point-free model |
| Finite crossing | `InvolutiveDistinction.existsBoundary_of_odd_natCard` | finite carrier via `Nat.card`, odd cardinality, involution | even two-state carrier |
| Boolean/K3 bridge | `LogicBridge.position_iff_determined` | Strong Kleene truth value | `position_unknown_counterexample` |
| Future distinction | `FutureDistinction.regular_iff_finite_future_states` | language over an alphabet; Myhill–Nerode bridge | non-regular languages remain outside finite quotient |
| Persistent identity | `Bisimulation.System.subset_bisimilar_of_postfixed` | observed transition system + post-fixed relation | observation/transition matching obligations are explicit |
| Viability | `Viability.ControlledSystem.kernel_fixed` | deterministic controlled system + safe set | recovery/viability separation model |
| Local sufficiency | `LocalSufficiency.sufficient_iff_not_ambiguous` | observation and required commitment | constant-observation insufficiency model |
| Conditional composition | `ConditionalComposition.witness_has_recovery` | already-constructed composition witness | construction theorem separately requires local sufficiency/coverage/compatibility/recoverability |
| Quantitative grounding | `QuantitativeGrounding.approximatelyGrounded_zero_iff` | fixed loss, experiment, prior, loss scale | binary 0–1-loss discard example gives strict positive gap |
| Evaluator migration | `EvaluatorMorphisms.hasVersionBridge_trans` | explicit judgment/goal-preserving bridge certificates | goal-only and goal-relevant countermodels |
| Grounded archive dynamics | `GroundedArchiveDynamics.novelCapability_of_groundedFrontierProgress` | goal reflects capability order + nonempty dominance-complete antichain frontier | grounded-progress/capability-novelty separations |
| Framework transport | `FrameworkMorphisms.FrameworkMorphism.preservesFeasibleSufficient` | derivation + realization/satisfaction preserving morphism | reflection countermodel shows preservation alone does not preserve dominance |
| Framework equivalence | `FrameworkMorphisms.FrameworkEquivalence.preservesDominance` | two-sided morphisms with inverse laws | one-way morphism countermodel |
| RSI invariant core | `RSIFrameworkMorphisms.morphismRoleCore_eq_legacy_fullCore` | certified advanced/next translations to shared role framework | legacy manual core is recovered exactly |
| Effective finitude boundary | `GuideCore.effectiveFinitude_does_not_imply_finite_state` | per-state finite effective capability sets | explicit infinite `Nat` state space |
| guide dependency spine | `GuideCore.conditionalComposition_minimal` | formal dependency graph only | corrigibility kept on independent branch |

## Classification policy

Repository research claims must remain classified as one of:

- **Established** — imported theorem/result from Mathlib or external literature,
  not claimed as proved here.
- **Proved here** — a theorem checked in this repository.
- **Conjecture / target** — research direction not yet proved.

No result should move from conjecture/target to proved-here status solely by
documentation changes.

## Assumption policy

For the freeze:

1. theorem signatures are the authoritative explicit mathematical assumptions;
2. `FreezeAudit.lean` records kernel axiom dependencies of the core;
3. `lake check` must accept the complete default target using only standard
   axioms;
4. `lake check --paranoid` must additionally be accepted by all independent
   checkers bundled with the selected stable Lean release;
5. necessity claims must retain a theorem-level countermodel or ablation result.
