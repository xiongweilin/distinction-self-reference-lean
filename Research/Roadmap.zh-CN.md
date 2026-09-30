# 收敛路线图

[English](Roadmap.md) | [简体中文](Roadmap.zh-CN.md)

本文记录项目从研究扩张阶段收敛到 v1.0 冻结的有限路线。计划中的主线已经完成；现在没有新的理论 PR 是 v1.0 的必要前置。

## PR #4 — 定量 Grounding

状态：**已合并。**

目标：从精确充分性 / 零 Bayes 风险，推进到决策相对的近似充分性。

完成内容包括：

- 按 loss 缩放的 Bayes risk gap / regret 上界；
- Markov 后处理下的单调性；
- 可加的组合误差界；
- 精确 task-family scheduling 判据；
- 严格反例。

当前实现刻意停留在 Blackwell–Le Cam 视角的 **risk side**；并不声称已经在 Lean 中形式化 total-variation deficiency 或完整 randomization theorem。

## PR #5 — Evaluator Morphism 与 Proof-Carrying Provenance

状态：**已合并。**

目标：把逐边 preservation predicate 提升成显式、可组合的结构。

已经包括：

- evaluator morphism；
- identity 与 composition；
- external goal preservation；
- 显式 bridge / preservation certificate；
- evidence 与 dependency transport；
- certificate composition；
- 说明只保持目标、不保持 judgment 仍不足够的反例。

因此 selective erasure 不再是临时策略：没有 bridge 的 evaluator-dependent evidence 会失去当前资格；独立 anchor evidence 可以保留；覆盖到的依赖链可以沿证书迁移。

## PR #6 — Self-Certification / Löb Boundary

状态：**因 toolchain 对齐而有意阻塞，见 issue #6。**

目标：把当前抽象 Löb 接口实例化到具体 formal-logic machinery，连接 reflection、Löb、Gödel II 与 Tarski 边界。

硬前提：本仓库与 `FormalizedFormalLogic/Foundation` 的 Lean / Mathlib pin 能兼容。

不能为了强行编译而削弱 trust assumptions。

## PR #7 — Grounded Branching 与 Archive Dynamics

状态：**已合并。**

目标：把 archive、changing evaluator 与 grounding 三条线合并，同时严格区分：

- archive 元素数量增长；
- Pareto/frontier 替换；
- evaluator 相对改进；
- 固定外部目标上的改进；
- 真正新的 capability。

已经补上 evaluator migration、evidence validity、morphism transport，以及两类长期停止条件。不能把 archive 变大直接当成 capability growth。

## PR #8 — Typed / Modal / Computational Self-Reference

状态：**延期到 v1.0 之后；draft 已关闭且未合并。**

只有在 typed partiality、later / guarded modality、effect 或 computability bridge 真正给出更尖锐的 self-application threshold 时，这条线才值得进入主干。

现有 draft 没有达到这个标准，因此不为了“路线图完整”而合并。

## PR #9 — Framework Morphism + guide Core

状态：**已合并。**

目标：用一般的结构保持翻译替代手工 role map。

已实现：

- condition / capability / realization map；
- derivability 与 condition satisfaction preservation；
- 由 realization transport 推出 compatibility preservation；
- identity / composition；
- sufficiency 与 feasible sufficiency transport；
- 为 dominance / equivalence transport 显式加入 derivation reflection；
- preservation 不足以保持 dominance 的 necessity countermodel；
- 由 certified morphism image 定义 invariant condition core。

对 `xiongweilin/guide` 只形式化具有明确数学意义的依赖主干，并刻意保护三条范围边界：

- effective finitude 不等于 `Fintype State`；
- reality 不被建模成可穷尽枚举的总状态；
- corrigibility 是独立增强支路，不是 agency 前置条件。

## v1.0 冻结

状态：**PR #10 已合并；仓库内容处于 pre-v1.0 frozen。正式 tag 仍等待稳定 Lean 4.35+ toolchain pin。**

没有新的理论 PR 是 v1.0 必需项。剩余必做工作只有 release toolchain stabilization 与在精确 pin 上重放全部检查。

冻结验收目标：

- 稳定 Lean / Mathlib pin；
- `lake build`；
- `lake check`；
- 全部独立 paranoid checker；
- 无 `sorry`；
- 无未声明 / 非预期 axiom；
- 核心 theorem assumptions 有索引；
- necessity claim 保留 theorem-level countermodel 或 ablation；
- Established / Proved here / Conjecture 严格分开；
- 稳定 public API 与明确 scope freeze。

## 依赖顺序

```text
PR #3 evaluator grounding
  ↓
PR #4 quantitative / task-family grounding
  ↓
PR #5 evaluator morphisms
  ├── PR #6 Löb / Foundation（toolchain 对齐后）
  ↓
PR #7 grounded archive dynamics
  ↓
PR #9 framework morphisms / guide core
  ↓
v1.0 freeze

PR #8 已延期到 mandatory v1.0 scope 之外。
```

## 与外部理论的定位

- Blackwell–Le Cam 理论为 PR #4 提供背景；当前 Lean 层先形式化 risk-bound 侧。
- proof-carrying-code 思路启发 PR #5 的显式可检查 bridge certificate，但 evaluator-morphism API 是本项目自己的。
- guarded recursion / later modality 启发过 PR #8，但标准 guarded fixed-point 结果本身不足以构成本项目的新贡献。
- institution morphism / comorphism 提供 PR #9 的邻近范式：跨逻辑系统翻译应显式保持 satisfaction 或 derivability 结构。
