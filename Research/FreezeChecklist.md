# v1.0 freeze checklist

[English](FreezeChecklist.md) | [简体中文](./FreezeChecklist.zh-CN.md)

Status: **PR #10 merged; repository content is pre-v1.0 frozen and the stable-release gate remains external.**

The repository currently uses Lean `4.35.0-rc3`. On 2026-09-30, Lean 4.35 has
not yet reached a stable release, so the final v1.0 toolchain pin and release tag
remain externally blocked. The project intentionally uses the 4.35
proof-checking pipeline and will not downgrade merely to claim a stable tag.

## Gates that can be completed before stable 4.35

- [x] PR #4 quantitative grounding merged.
- [x] PR #5 evaluator morphisms merged.
- [x] PR #7 grounded archive dynamics merged.
- [x] PR #9 framework morphisms / guide core merged.
- [x] PR #6 isolated behind an explicit Foundation toolchain gate.
- [x] PR #8 closed and deferred beyond v1.0 after producing no sharper self-application threshold.
- [x] project Lean source currently contains no `sorry` or `admit`.
- [x] project Lean source currently declares no project-local `axiom` or
      `constant`.
- [x] v1.0 core theorem names and explicit assumption scopes indexed.
- [x] CI: `lake build`.
- [x] CI: elaborate `FreezeAudit.lean` and print core theorem axioms.
- [x] CI: kernel replay of the exact build export via `lake check --from-export`.
- [x] CI: complete the full bundled paranoid checker set on the exact build export: Lean paranoid kernel, `lean4lean`, `nanoda`, `con-leche`, and `con-ron`. PR #10 validated the full-export checkers plus dependency-closed nanoda shards in independent sandboxed jobs.
- [x] CI: comment/string-aware source audit rejects future `sorry`, `admit`, `axiom`, and
      `constant` declarations.
- [x] documented v1.0 public core surface designated in `Research/CoreTheoremIndex.md` and guarded by `FreezeAudit.lean`.

## Final stable-release gates

These must remain unchecked until Lean 4.35 stable exists.

- [ ] pin Lean to stable `v4.35.0` (or a later explicitly chosen stable
      release) rather than an RC;
- [ ] update/pin the compatible Mathlib revision;
- [ ] regenerate and commit the intended dependency manifest for the release;
- [ ] rerun build, kernel check, and paranoid independent replay on the exact
      release pin;
- [ ] verify PR #6/Foundation compatibility again; inclusion in v1.0 remains
      optional unless the toolchains align without weakening trust assumptions;
- [ ] tag `v1.0` only after all mandatory gates above pass.

## Scope freeze

v1.0 is a formal research artifact about a branching family of self-reference
frameworks and the conditions connecting them. It is not a claim that one of
those frameworks is the unique ontology of reality, consciousness, agency, or
physics.

The following remain outside mandatory v1.0 scope:

- full Spencer-Brown primary-algebra quotient/equational theory;
- full Varela calculus;
- Schwartz derivability-preserving isomorphisms;
- Foundation/Löb integration while toolchains are incompatible;
- PR #8 typed/modal results unless they establish a genuinely sharper
  self-application threshold before the final freeze.
