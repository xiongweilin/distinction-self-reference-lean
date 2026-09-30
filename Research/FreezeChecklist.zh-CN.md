# v1.0 冻结检查表

[English](FreezeChecklist.md) | [简体中文](FreezeChecklist.zh-CN.md)

状态：**PR #10 已合并；仓库内容已进入 pre-v1.0 freeze，稳定 release gate 仍由外部 toolchain 决定。**

仓库当前使用 Lean `4.35.0-rc3`。截至 2026-09-30，Lean 4.35 还没有 stable release，因此最终 v1.0 toolchain pin 与 release tag 仍被外部条件阻塞。本项目有意使用 Lean 4.35 的 proof-checking pipeline，不会为了提前打 stable tag 而降级。

## stable 4.35 之前已经完成的 gate

- [x] PR #4 quantitative grounding 已合并。
- [x] PR #5 evaluator morphism 已合并。
- [x] PR #7 grounded archive dynamics 已合并。
- [x] PR #9 framework morphism / guide core 已合并。
- [x] PR #6 被显式隔离到 Foundation toolchain gate。
- [x] PR #8 已关闭并延期到 v1.0 之后。
- [x] 项目 Lean 源码没有 `sorry` / `admit`。
- [x] 项目源码没有 project-local `axiom` / `constant` 声明。
- [x] v1.0 核心 theorem 名和显式 assumption scope 已建立索引。
- [x] CI 执行 `lake build`。
- [x] CI elaboration `FreezeAudit.lean` 并打印核心 theorem axioms。
- [x] 从 exact build export 运行 `lake check --from-export`。
- [x] exact export 通过 Lean paranoid kernel、`lean4lean`、`nanoda`、`con-leche`、`con-ron`；其中 nanoda 使用 dependency-closed shards。
- [x] comment/string-aware source audit 拒绝未来引入 `sorry`、`admit`、`axiom` 和 `constant`。
- [x] `Research/CoreTheoremIndex.md` 与 `FreezeAudit.lean` 固定公开 core surface。

## 最终 stable-release gate

在 stable Lean 4.35+ 出现并被明确选定前，这些项目保持未勾选：

- [ ] 把 Lean pin 从 RC 改成选定 stable release；
- [ ] 更新并固定兼容 Mathlib revision；
- [ ] 重新生成并提交 release 使用的 dependency manifest；
- [ ] 在精确 release pin 上重跑 build、kernel check 与所有独立 replay；
- [ ] 再检查 PR #6 / Foundation compatibility；即使 toolchain 对齐，是否纳入 v1.0 仍可保持可选；
- [ ] 全部 mandatory gate 通过后再打 `v1.0` tag。

## scope freeze

v1.0 是关于多条自指框架分支以及连接条件的形式研究 artifact。它不是在宣称某一框架是现实、意识、行动者或物理的唯一 ontology。

以下内容不属于 mandatory v1.0 scope：

- 完整 Spencer-Brown primary-algebra quotient / equational theory；
- 完整 Varela calculus；
- Schwartz derivability-preserving isomorphism；
- toolchain 不兼容期间的 Foundation / Löb concrete integration；
- 没有产生更尖锐阈值的 typed/modal 扩展。
