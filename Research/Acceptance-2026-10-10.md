# Formal research branch — merge acceptance record

Date: 2026-10-10. Scope: **formal research merge** only. This is not the v1.0 stable-toolchain release gate.

## Reproducible evidence

- Repository `xiongweilin/distinction-self-reference-lean`, PR [#15](https://github.com/xiongweilin/distinction-self-reference-lean/pull/15).
- Examined source commit `b3b882068069277538187965212ad48a999515da`; base `9cebbddd855befa1dfa8e91189dac8325a23c46d`.
- [GitHub Actions 38051306157](https://github.com/xiongweilin/distinction-self-reference-lean/actions/runs/38051306157): **14/14 passing** on this source — root Lean build, eight nanoda shards, lean-paranoid, lean4lean, con-leche, con-ron and kernel-replay. Source and toolchain versions are bound to that run.
- `DistinctionSelfReference/RobustAction.lean` proves: `safe_for_actual` if actual world belongs to the supplied possibility set; `survives_information_refinement` when the latter is a subset; `commonSafe_union_iff`; examples with and without any common action.
- `GuideCore.required` changes the dependency graph to make reflexive self-model conditions optional for elementary bounded action. The model-relative result is **not** a proof that reality supplies a correct bound, authorization, or a particular normative system.

## Freeze and acceptance boundary

Changes to `GuideCore.required` are **semantic**. The historical v1.0 theorem index remains an archived specification snapshot and cannot be treated as unchanged formal semantics. The new graph and `RobustAction` explicitly belong to a post-freeze research proposal. Merging into `main` changes the development line but does not mint a v1.0 release or certify stable/Foundation interoperability.

Merge is acceptable only as *research* after checks stay green on the final documentation-containing tree. A v1.0 release still requires separate toolchain pin migration, full stable checker evidence and independent Foundation compatibility acceptance, plus an explicit review of the revised GuideCore's release scope.

## Claim decision

- **Accepted:** the listed conditional Lean statements typecheck and pass the independent replay/checker matrix at the tested pin.
- **Not accepted:** real-world safety, universally necessary/non-necessary metaphysics, runtime execution correctness, real human benefit, stable v1.0 release readiness.
