# v1.0 freeze checklist

Status: **pre-freeze hardening in PR #10; stable-release gate remains external.**

The repository currently uses Lean `4.35.0-rc3`. On 2026-09-30, Lean 4.35 has
not yet reached a stable release, so the final v1.0 toolchain pin and release tag
remain externally blocked. The latest stable Lean release is 4.34.1, but this
project intentionally uses the 4.35 proof-checking pipeline and will not
downgrade merely to claim a stable tag.

## Gates that can be completed before stable 4.35

- [x] PR #4 quantitative grounding merged.
- [x] PR #5 evaluator morphisms merged.
- [x] PR #7 grounded archive dynamics merged.
- [x] PR #9 framework morphisms / guide core merged.
- [x] PR #6 isolated behind an explicit Foundation toolchain gate.
- [x] PR #8 isolated as a non-blocking draft.
- [x] project Lean source currently contains no `sorry` or `admit`.
- [x] project Lean source currently declares no project-local `axiom` or
      `constant`.
- [x] v1.0 core theorem names and explicit assumption scopes indexed.
- [x] CI: `lake build`.
- [x] CI: elaborate `FreezeAudit.lean` and print core theorem axioms.
- [x] CI: kernel replay of the exact build export via `lake check --from-export`.
- [ ] CI: complete the full bundled paranoid checker set on the exact build export: Lean paranoid kernel, `lean4lean`, `nanoda`, `con-leche`, and `con-ron`. GitHub CI runs these as independent sandboxed jobs because the combined upstream sequence exceeds the hosted runner lifetime.
- [x] CI: comment/string-aware source audit rejects future `sorry`, `admit`, `axiom`, and
      `constant` declarations.

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
- [ ] freeze the documented public core API;
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
