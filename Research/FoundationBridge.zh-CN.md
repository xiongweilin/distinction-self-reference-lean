# self-certification 边界与 Foundation 桥

[English](FoundationBridge.md) | [简体中文](FoundationBridge.zh-CN.md)

RSI 的信任层不应该自己重新实现算术元数学。

## 上游形式化

[FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation) 已经在 Lean 4 中形式化本项目关心的几类元逻辑结果：

- `Foundation/FirstOrder/Incompleteness/Löb.lean`
  - `FFL.FirstOrder.Arithmetic.löb_theorem`
  - 大意：如果理论能证明“可证的 σ 蕴含 σ”，那么理论能证明 σ。
- `Foundation/FirstOrder/Incompleteness/Second.lean`
  - `FFL.FirstOrder.Arithmetic.consistent_unprovable`
  - 对满足相应算术理论条件的 Gödel 第二不完备性结果。
- `Foundation/FirstOrder/Incompleteness/Tarski.lean`
  - `FFL.FirstOrder.Arithmetic.undefinability_of_truth`
  - 排除相应统一形式的算术真理谓词。
- `Foundation/FirstOrder/Incompleteness/First.lean`
  - Gödel 第一不完备性以及真但不可证句子的相关结果。

## 当前集成状态

本仓库目前固定：

- Lean `v4.35.0-rc3`；
- 与该 toolchain 对应的一个 Mathlib commit。

Foundation 的默认分支目前固定：

- Lean `v4.34.0`；
- Mathlib `v4.34.0`。

因此暂不直接加入 Lake dependency。这里宁可等待工具链兼容，也不通过降低任一边的信任边界来强行编译。

## 本仓库的局部抽象

`DistinctionSelfReference/SelfCertificationBarrier.lean` 只定义 RSI 层真正需要的接口：

- provability predicate；
- provability box；
- implication；
- Löb rule。

局部定理 `reflection_collapses_to_proof` 以后应该由 Foundation 的 `löb_theorem` 实例化；它不是 Löb 定理的替代证明。

同一文件还区分：

1. 内部认证；
2. 语义 soundness；
3. soundness transfer；
4. 外部 grounding。

有限反例说明：所有 verifier 都能自认证，并不保证它们在语义上健全。另一方面，只要给出一个非循环的 grounded root，再加上语义 soundness transfer，就能沿迁移链传播 soundness。

## 后续桥接

等 Foundation 发布与本仓库 Lean / Mathlib pin 兼容的版本后，再：

- 加入精确固定的依赖；
- 用 arithmetic provability machinery 实例化抽象 `LobInterface`；
- 把具体 verifier-soundness sentence 接到 Löb、Gödel II 和 Tarski 边界。

目标不是宣传“verifier 不能证明自己正确”这一口号，而是精确刻画：哪些 verifier migration / reflection 接口满足这些元逻辑定理的前提。
