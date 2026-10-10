# Lean 中的区分与自指

[English](README.md) | [简体中文](README.zh-CN.md)

这是一个形式化研究项目，用来研究：从最弱的区分与再进入结构出发，逐步增加哪些条件，会得到更强的自指、持续性、行动、验证、评价与递归自修改结构。

项目刻意区分三类内容：

1. **已有结果**：来自数学文献、Mathlib 或其他形式化工作的既有定理；
2. **本仓库证明的模型与定理**：在 Lean 中检查过的结果；
3. **尚未证明的方向**：只作为研究目标或冻结范围之外的后续问题。

本项目不把任何一个模型解释成“区分”或“自指”的唯一含义。

## 已验证结果的最小概览

本仓库证明的是**带有明确前提的数学命题**；它没有证明现实世界存在唯一的区分本体，也没有验证 guide 的真实决策收益或开放式递归自我改进必然安全。

- **对合 crossing**：状态只能是固定点或二周期；有限奇数载体必须有固定点。
- **对角自指**：Lawvere 型固定点需要表示性/对角条件，两状态交换本身不能推导普遍自指。
- **判断充分性**：观测相对的承诺充分性是因子化条件，不能替代 guide 的三值解释性判断或现实效果测量。
- **组合**：局部性质的组合依赖覆盖、交叠一致性及相应恢复条件。
- **验证与改进迁移**：结论依赖显式的信任锚、目标保持、证据新鲜度或资源假设；证明不会凭空提供这些前提。

精确核心定理、假设与边界反例见 [v1.0 核心定理索引](Research/CoreTheoremIndex.zh-CN.md)；所有编译模块见 [`DistinctionSelfReference.lean`](DistinctionSelfReference.lean) 的 import 列表；其他研究分支见 [Candidates](Research/Candidates.zh-CN.md)，发布门槛见 [冻结清单](Research/FreezeChecklist.zh-CN.md)。

## 仓库结构

Lean 源码位于 `DistinctionSelfReference/`。根模块 `DistinctionSelfReference.lean` 导入公开库模块；`FreezeAudit.lean` 仅用于 CI 的冻结审计，不由根模块导入。

主要模块可以按问题分成几组：

- **最小区分与逻辑桥**：`Core`、`Finite`、`TwoState`、`Dynamic`、`ThreeState`、`PrimaryBoolean`、`KleeneThree`、`LogicBridge`；
- **未来、同一性与控制**：`FutureDistinction`、`Bisimulation`、`LabeledBisimulation`、`FutureBisimulation`、`Viability`、`Recovery`、`Purposeful`、各类 gluing / control 模块；
- **充分性与信息**：`LocalSufficiency`、`AnchorMinimality`、`CompositionalSufficiency`、`ConditionalComposition`、`InformationOrder`、`MarkovGarbling`、`StochasticAnchorGrounding`、`QuantitativeGrounding`；
- **自修改与 RSI**：`SelfModification`、`VerifiedUpgrade`、`VerifierMigration`、`GuardedRSI`、`TrustedKernel`、`TrustedKernelMigration`、资源、信任、能力增长与 archive 模块；
- **变化 evaluator 与 grounding**：`ChangingEvaluator`、`EvaluatorGrounding`、`EvaluatorProvenance`、`EvaluatorMorphism`、`MorphismProvenance`、`EvidenceDependency`、`DynamicAnchorGrounding`、`TaskRelativeScheduling`、`TaskFamilyScheduling`、`GroundedArchiveDynamics`；
- **表示型自指**：`OrderTheoretic`、`Representational`、`RepresentationalObstruction`、`WeakRepresentation`、`PartialLawvere`、`GuardedLawvere`、`Computability`；
- **元框架与 guide 桥**：`MetaFramework`、`FrameworkMorphism`、`RSIFrameworkMorphisms`、`GuideCore`。

研究文档：

- [已有结果](Research/Established.zh-CN.md)
- [候选命题与框架阶梯](Research/Candidates.zh-CN.md)
- [Foundation / Löb 桥](Research/FoundationBridge.zh-CN.md)
- [收敛路线图](Research/Roadmap.zh-CN.md)
- [v1.0 核心定理索引](Research/CoreTheoremIndex.zh-CN.md)
- [v1.0 冻结检查表](Research/FreezeChecklist.zh-CN.md)

## 当前状态

计划中的收敛阶段已经完成：

- PR #4：定量 grounding，已合并；
- PR #5：evaluator morphism 与 proof-carrying provenance，已合并；
- PR #7：grounded branching / archive dynamics，已合并；
- PR #9：framework morphism 与 guide core，已合并；
- PR #10：v1.0 冻结前 proof hardening，已合并。

因此仓库已经处于 **content-complete / pre-v1.0 frozen** 状态。v1.0 之前不再要求新增理论结果。

仍有两个明确的范围外事项：

- issue #6：等待 `FormalizedFormalLogic/Foundation` 与本仓库 Lean / Mathlib toolchain 可兼容后，再做具体 Löb / Gödel / Tarski 实例化；
- typed / modal / computational self-reference 的 draft 已关闭，因为没有得到比现有 partial / guarded Lawvere 更尖锐的新阈值结果。

最终 v1.0 还需要把 toolchain 从 Lean `4.35.0-rc3` 切到选定的稳定 Lean 4.35+ 与兼容 Mathlib，然后在该精确 pin 上重新执行完整检查并打 tag。

## 范围警告

本仓库**不是** Spencer-Brown《Laws of Form》的完整形式化，也不是 Varela calculus 的完整形式化；RSI 部分同样不是“开放式递归自我改进已经成立”的证明。

`InvolutiveDistinction` 只捕捉 crossing 风格的对合结构。`PrimaryBoolean` 只提供 primary-shaped 语法与布尔语义，而没有完成 primary algebra 的商结构 / 等式理论。`KleeneThree` 与 `LogicBridge` 只证明 Strong Kleene 语义侧和确定值片段上的保守桥。

完整 Varela syntax、Schwartz 的 derivability-preserving isomorphism、以及被延期的 typed/modal 扩展，都不在冻结的 v1.0 必要范围内。
