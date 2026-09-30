# Foundation bridge for self-certification limits

The RSI trust layer should not reimplement arithmetic metamathematics.

## Upstream formalization

The repository [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation) already formalizes the relevant meta-logical results in Lean 4:

- `Foundation/FirstOrder/Incompleteness/Löb.lean`
  - `FFL.FirstOrder.Arithmetic.löb_theorem`
  - shape: if the theory proves `Prov(σ) → σ`, then it proves `σ`.
- `Foundation/FirstOrder/Incompleteness/Second.lean`
  - `FFL.FirstOrder.Arithmetic.consistent_unprovable`
  - Gödel's second incompleteness theorem for the stated arithmetic-theory hypotheses.
- `Foundation/FirstOrder/Incompleteness/Tarski.lean`
  - `FFL.FirstOrder.Arithmetic.undefinability_of_truth`
  - no arithmetical truth predicate of the stated uniform form.
- `Foundation/FirstOrder/Incompleteness/First.lean`
  - Gödel incompleteness results and true-but-unprovable sentence theorems.

## Current integration status

This repository currently pins:

- Lean `v4.35.0-rc3`
- a Mathlib commit on that toolchain.

Foundation master currently pins:

- Lean `v4.34.0`
- Mathlib `v4.34.0`.

Therefore a direct Lake dependency is intentionally deferred rather than forcing the whole project onto a mismatched toolchain.

## Local abstraction

`DistinctionSelfReference/SelfCertificationBarrier.lean` introduces only the interface needed by the RSI layer:

- a provability predicate,
- a provability-box constructor,
- implication,
- Löb's rule.

The local theorem `reflection_collapses_to_proof` should later be instantiated from Foundation's `löb_theorem`; it is not intended as a replacement proof of Löb.

The same file separates:

1. internal certification,
2. semantic soundness,
3. soundness transfer,
4. external grounding.

A finite countermodel proves that universal self-certification can coexist with semantic unsoundness. A grounded-chain theorem shows exactly where the non-circular premise enters.

## Next bridge

When Foundation publishes a revision compatible with this repository's Lean/Mathlib toolchain, add it as a pinned dependency and instantiate the abstract `LobInterface` from the arithmetic provability machinery. Then connect a concrete verifier-soundness sentence to:

- Löb barrier,
- Gödel II consistency limits,
- Tarski truth undefinability.

The target is not the slogan "a verifier cannot prove itself sound"; the target is a precise characterization of which verifier-migration/reflection interface satisfies the hypotheses of these theorems.
