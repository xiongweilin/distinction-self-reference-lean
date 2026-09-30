# v1.0 核心定理索引

[English](CoreTheoremIndex.md) | [简体中文](CoreTheoremIndex.zh-CN.md)

本文定义 **v1.0 core**，用于冻结期的名称稳定性和假设审查。它不是说列表之外的定理不重要，而是选出一组公开横截面，要求这些 theorem 名、作用范围和显式假设在冻结过程中保持稳定。

机器可检查的对应文件是 `DistinctionSelfReference/FreezeAudit.lean`。CI 会单独 elaboration 它，并打印这里每个核心 theorem 的 kernel axiom 依赖。

| 领域 | 核心 theorem | 显式假设 / 范围 | necessity / boundary witness |
| --- | --- | --- | --- |
| 最小区分 | `InvolutiveDistinction.boundary_or_twoCycle` | 一个 involutive crossing | 两状态无固定点模型 |
| 有限 crossing | `InvolutiveDistinction.existsBoundary_of_odd_natCard` | `Nat.card` 有限、奇数基数、对合 | 偶数两状态模型 |
| Boolean/K3 桥 | `LogicBridge.position_iff_determined` | Strong Kleene truth value | `position_unknown_counterexample` |
| 未来区分 | `FutureDistinction.regular_iff_finite_future_states` | alphabet 上的 language；Myhill–Nerode 桥 | 非正则 language 不落入有限商 |
| 持续同一性 | `Bisimulation.System.subset_bisimilar_of_postfixed` | 带观测转移系统 + post-fixed relation | observation / transition matching obligation 显式存在 |
| 生存性 | `Viability.ControlledSystem.kernel_fixed` | deterministic controlled system + safe set | recovery / viability separation model |
| 局部充分性 | `LocalSufficiency.sufficient_iff_not_ambiguous` | observation + required commitment | constant-observation insufficiency model |
| 条件性组合 | `ConditionalComposition.witness_has_recovery` | 已构造的 composition witness | 构造 theorem 另需 local sufficiency / coverage / compatibility / recoverability |
| 定量 grounding | `QuantitativeGrounding.approximatelyGrounded_zero_iff` | 固定 loss、experiment、prior、loss scale | Boolean 0–1 loss discard example 给出严格正 gap |
| evaluator migration | `EvaluatorMorphisms.hasVersionBridge_trans` | 显式保持 judgment / goal 的 bridge certificate | goal-only 与 goal-relevant countermodel |
| grounded archive | `GroundedArchiveDynamics.novelCapability_of_groundedFrontierProgress` | goal 反射 capability order + 非空 dominance-complete antichain frontier | grounded progress / novelty separation |
| framework transport | `FrameworkMorphisms.FrameworkMorphism.preservesFeasibleSufficient` | 保持 derivation、realization / satisfaction 的 morphism | reflection countermodel |
| framework equivalence | `FrameworkMorphisms.FrameworkEquivalence.preservesDominance` | 双向 morphism + inverse laws | one-way morphism countermodel |
| RSI invariant core | `RSIFrameworkMorphisms.morphismRoleCore_eq_legacy_fullCore` | advanced / next RSI 到共享 role framework 的 certified translations | 精确恢复旧手工 core |
| effective finitude 边界 | `GuideCore.effectiveFinitude_does_not_imply_finite_state` | 每状态有效 capability set 有限 | 显式无限 `Nat` state space |
| guide 依赖主干 | `GuideCore.conditionalComposition_minimal` | 形式 dependency graph 内 | corrigibility 保持独立支路 |

## 分类规则

研究主张必须保持在下面三类之一：

- **Established**：来自 Mathlib 或外部文献的已有 theorem / formalization；
- **Proved here**：由本仓库 Lean 检查的 theorem；
- **Conjecture / target**：尚未证明的研究方向。

不能只靠修改文档把一个 target 升级成 proved-here。

## 假设与冻结规则

1. theorem signature 是显式数学假设的权威来源；
2. `FreezeAudit.lean` 记录核心 theorem 的 kernel axiom dependency；
3. `lake check` 必须接受整个默认 target；
4. 独立 checker 必须在选定 stable toolchain 上重放通过；
5. necessity claim 必须保留 theorem-level countermodel 或 ablation result。
