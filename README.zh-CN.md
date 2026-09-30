# Lean 中的区分与自指

[English](README.md) | [简体中文](README.zh-CN.md)

这是一个形式化研究项目，用来研究：从最弱的区分与再进入结构出发，逐步增加哪些条件，会得到更强的自指、持续性、行动、验证、评价与递归自修改结构。

项目刻意区分三类内容：

1. **已有结果**：来自数学文献、Mathlib 或其他形式化工作的既有定理；
2. **本仓库证明的模型与定理**：在 Lean 中检查过的结果；
3. **尚未证明的方向**：只作为研究目标或冻结范围之外的后续问题。

本项目不把任何一个模型解释成“区分”或“自指”的唯一含义。

## 形式化阶梯

| 框架 | 增加的条件 | 主要结果 |
| --- | --- | --- |
| 核心 crossing | crossing 是对合 | 每个状态要么是固定边界，要么属于非平凡二周期 |
| 有限 crossing | 有限载体 + 对合 | 无固定点的有限载体基数为偶数；奇数载体必有固定点 |
| 两状态 | 恰有两个状态，crossing 交换二者 | 无静态固定点；交换是唯一无固定点自映射 |
| 动态两状态 | 反复迭代交换 | 每条轨道的精确周期为二 |
| 三状态 | 增加一个自对偶边界状态 | 恰有一个静态固定点 |
| Primary Boolean 核心 | blank / juxtaposition / crossing / 变量 | 与 false / OR / NOT 原始语法双向翻译，并保持语义 |
| Strong Kleene 核心 | 三值 K3 | 三状态 crossing 对应 K3 否定；unknown 是唯一固定点 |
| Boolean → K3 | 在 K3 中解释同一语法 | 对布尔赋值是保守扩展；排中式位置公式恰在取值已确定时为真 |
| 序理论 | 完备格 + 单调自映射 | 由 Knaster–Tarski 得到最小和最大固定点 |
| 表示型自指 | 满射内部 evaluator | 被表示结果类型的每个自映射都有固定点 |
| 表示障碍 | 结果类型存在无固定点自映射 | 不可能有 Lawvere 型的全满射自表示 |
| 弱表示 | 只表示某个 endomap 对应的对角函数 | 单个关键对角函数可表示就足以迫出固定点 |
| 语义不相容 | 条件解释到共同 realization | 无固定点 endomap 与全满射表示可形成显式不相容条件对 |
| 未来区分 | 历史 + 后续 continuation 测试 | 两段历史未来不可区分当且仅当所有 continuation 都同意；有限商对应正则性 |
| 双模拟 | 带观测的转移系统 | 持续的行为同一性是最大固定点，并有共归纳原理 |
| 标号双模拟桥 | canonical residual DFA + 标号保持 | 未来不可区分恰对应 canonical labelled bisimilarity |
| 生存性 | 行动 + 安全集 | 可持续行动区域是安全前驱算子的最大固定点 |
| 恢复性 | 有限行动计划 + 生存核 | 生存状态都可恢复；反向不成立 |
| 目的相对生存性 | 同一动力学 + 不同可接受方向 | 放宽目的会单调扩大生存与恢复能力 |
| 目的相对能力 | 固定动力学 + 行动相关区分 | 只改变目的方向就可能改变能力核 |
| 局部 / 全局 | 局部约束族 | 两两相容仍可能没有全局见证 |
| 嵌套拼接 | 有限非空线序 + 嵌套约束 | 局部可满足即可得到全局见证 |
| 重叠拼接 | 局部作用域 + 覆盖 + 重叠一致 | 无需嵌套也可构造全局赋值 |
| 局部充分性 | 观测 + 所需承诺 | 充分性等价于所需承诺可经观测因子化，也等价于不存在歧义见证 |
| 组合充分性 | 局部充分 + 覆盖 + 重叠相容 | 局部承诺可拼成由组合观测解码的全局承诺 |
| 条件性组合 | 组合充分 + 有限恢复性 | 构造全局承诺，并附带回到生存区域的恢复路径 |
| 确定性信息序 | 表示 + 后处理因子化 | 后处理不能创造新区分，并存在严格信息损失 |
| Markov garbling | 实验 + Markov 后处理 | Bayes 风险不能改善，风险型信息与 KL 散度不能增加 |
| 信息 → 未来桥 | 粗表示经 residual language 因子化 | 未来等价在这类摘要下保持 |
| 控制抽象 | 动力学交换 + 安全保持 / 反射 | 分别得到能力的前向保持、反向反射以及双向精确性 |
| 定向控制模拟 | 不同 action 类型 + 前后向步模拟 | 前向条件保持能力，后向条件反射能力 |
| 安全信息充分性 | 抽象纤维 + 安全标签因子化 | 安全纤维不变性与安全位可因子化等价 |
| 控制条件消融 | 分别删除模拟 / 安全条件 | 每项条件都有独立反例说明不能随意删除 |
| 控制依赖图 | 四个控制条件 + 四类方向能力 | 给出具体 inclusion-minimal 条件集 |
| 元框架 | 单调 condition→capability 图 + 条件语义 | 消融最小性与包含最小性对应，并形式化相容、不相容、支配与能力等价 |
| 可计算自指 | 程序码 + evaluator + 可计算性 | 接到 Rogers 固定点与 Kleene 第二递归定理 |
| 完整版本递归诊断 | 非退化 self-modifier + 完整版本身份 | 版本复现段必为能力平台；版本周期不等于 modifier 固定点 |
| 无限期可调用性 | proposal 流 + 证明成本 + 时变预算 | 有统一证明成本上界且预算覆盖时，可无限期调用；仅有认证不足以保证可调用 |
| trusted-kernel 迁移 | checker 版本 + 前驱核验 handoff | 初始信任可沿迁移传播，并保持目标 invariant soundness |
| 联合 RSI 收敛 | 能力 / 信任 / 现实三条序列 | 三者的最终稳定可组合 |
| 变延迟现实核验 | 任意 source schedule + eventual freshness | 最终稳定要求可穿过变延迟和乱序；永久陈旧给出反例 |
| 内生验证资源 | 预算 + 检查成本 + 再生 | 自我维持的资源条件可保证无限期可调用 |
| 信任委派 | checker 健康状态 + 重叠批准 | 至少一个健康重叠 checker 时可传递 soundness |
| 无限能力序 | 有限 / 无限能力宇宙 | 有限宇宙禁止无限处处严格增长；Nat 能力给出显式无限严格链 |
| RSI invariant core | 不同 trust architecture 的角色翻译 | 可抽取共同 trust anchor 与 soundness transfer 等结构 |
| 精确调度判据 | 变延迟 / 乱序 source schedule | eventual freshness 当且仅当所有最终稳定布尔要求都能被调度保持 |
| 资源生存性 | 受控预算状态 | 可持续验证预算恰是一个 viability kernel |
| 阈值信任 | 有限 quorum + compromise 上界 | 足够大 quorum 且被破坏成员少于阈值时必有健康批准者 |
| 排名化能力增长 | 严格增长反映到良基顺序 | 良基 rank 排除无限严格能力增长；显式无限链排除这类 rank |
| 自认证边界 | 内部认证 + 语义 soundness + 抽象 Löb 规则 | 全部自认证可与语义不健全共存；非循环 grounding 可恢复 soundness transfer |
| 变化 evaluator | 时变局部改进关系 | 存在统一严格传递扩展当且仅当局部边并的传递闭包无环；有限状态时等价于 Nat 公共势函数 |
| evaluator grounding | 固定外部目标 + anchor + 时变 evaluator | 足够 anchor 与 evaluator soundness 可把局部改进提升为固定外部目标上的改进；不足 anchor 可导致 proxy regression |
| evaluator provenance | 版本化 evaluator 证据 + anchor 证据 | 历史保留与当前资格分离；满足保持条件时才能迁移旧判断 |
| 动态 anchor grounding | 延迟 / 乱序观测 | universal stable-task preservation 与 eventual freshness 精确对应 |
| 任务相对调度 | 固定最终稳定任务 + schedule | universal freshness 推出任务保持，但单个任务可在不 fresh 的 schedule 下仍被保持 |
| 随机 anchor grounding | experiment + prior + loss + garbling | 后处理不能创造零 Bayes 风险 grounding |
| 依赖感知 provenance | 证据依赖图 + 版本资格 | 陈旧 premise 会沿传递依赖使结论失效；独立 anchor 路径可继续有效 |
| 分支 / archive RSI | 复现分支 + 保留 archive | 分支平台与 archive 严格增长可并存；WQO 只给出特定 antichain 稳定结论 |
| 部分 Lawvere | Option evaluator + 对角表示 | 关键对角自应用一旦有定义就迫出固定点 |
| guarded Lawvere | 显式 self-application guard | guard 打开时迫出固定点；无固定点映射要求该 guard 关闭 |
| 定量 grounding | 决策实验 + 参考实验 + 风险差上界 | 精确 grounding 是零误差特例；风险差界具有单调、组合和 garbling 边界 |
| 任务族调度 | 最终稳定任务族 + source schedule | 对给定任务族有精确保持判据；取全部稳定布尔任务时恢复 eventual freshness |
| evaluator morphism | evaluator/state 映射 + preservation certificate | judgment / goal 保持可组合，并可迁移证据与依赖 |
| grounded archive dynamics | archive/frontier + evaluator + 外部目标 + 能力序 | archive 增长、frontier 替换、evaluator 改进、固定目标改进与能力 novelty 被严格区分 |
| framework morphism | condition / capability / realization 映射 + 保持律 | 充分性与相容性可组合传输；reflection / equivalence 控制更强不变量 |
| guide dependency core | guide 中具有明确数学含义的依赖主干 | 形式化最小自指、连续性、行动、有效有限性、目的、局部充分性与纠错支路，同时不把现实压成有限总状态 |

这是一棵分支化的阶梯。静态固定点、周期复现、序理论固定点、对角固定点和可计算固定点不能在没有桥接证明时被当成同一种东西。

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
