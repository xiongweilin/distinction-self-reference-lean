# Formal research branch — merge acceptance record

Date: 2026-10-10. Scope: **formal research merge** only. This is not the v1.0 stable-toolchain release gate.

## Reproducible evidence

- Repository `xiongweilin/distinction-self-reference-lean`, PR [#15](https://github.com/xiongweilin/distinction-self-reference-lean/pull/15).
- Examined source commit `b3b882068069277538187965212ad48a999515da`; base `9cebbddd855befa1dfa8e91189dac8325a23c46d`.
- [GitHub Actions 38051306157](https://github.com/xiongweilin/distinction-self-reference-lean/actions/runs/38051306157): **14/14 passing** on this source — root Lean build, eight nanoda shards, lean-paranoid, lean4lean, con-leche, con-ron and kernel-replay. Source and toolchain versions are bound to that run.
- `DistinctionSelfReference/RobustAction.lean` proves: `safe_for_actual` if actual world belongs to the supplied possibility set; `survives_information_refinement` when the latter is a subset; `commonSafe_union_iff`; examples with and without any common action.
- **Freeze-compatible architectural correction:** the original `GuideCore.required` is restored *verbatim*. A separate `ActionFirstGuideCore.required` carries the new graph with a strict-weakening theorem showing a genuine difference in prerequisites. No v1.0 theorem dependency is silently changed. The model-relative result does not prove actual reality bounds or authorizations.

## Freeze and acceptance boundary

`GuideCore.required` and existing v1.0 theorem contracts remain **unchanged**. The `ActionFirstGuideCore` graph and `RobustAction` are additive post-freeze research results. Merging does not mint v1.0 or certify stable/Foundation interoperability.

Merge is acceptable only as *research* after checks stay green on the final documentation-containing tree. A v1.0 release still requires separate toolchain pin migration, full stable checker evidence and independent Foundation compatibility acceptance, while keeping all new action-first results outside that frozen release scope.

## Claim decision

- **Accepted:** the listed conditional Lean statements typecheck and pass the independent replay/checker matrix at the tested pin.
- **Not accepted:** real-world safety, universally necessary/non-necessary metaphysics, runtime execution correctness, real human benefit, stable v1.0 release readiness.
