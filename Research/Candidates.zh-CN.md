# 候选命题与框架阶梯

[English](Candidates.md) | [简体中文](Candidates.zh-CN.md)

本文记录本仓库的命题阶梯、已证明结果、已有外部结果以及冻结范围之外的方向。

状态标签：

- **本仓库已证明**：由本仓库 Lean 检查；
- **外部已有**：已有数学定理或其他形式化，本仓库只做实例化 / 桥接；
- **部分完成**：只完成目标的一部分；
- **目标 / 延期方向**：尚未证明，不属于冻结的 v1.0 结果集，除非以后由 checked theorem 明确升级。

## 第 0 层：最小 crossing

### P0.1 — 两状态唯一性
**本仓库已证明**：`TwoState.eq_cross_of_fixedPointFree`。

### P0.2 — 对合轨道分解
**本仓库已证明**：`InvolutiveDistinction.boundary_or_twoCycle`。每个状态要么是固定边界，要么属于非平凡二周期。

### P0.3 — 有限奇偶定理
**本仓库已证明**：无固定点有限对合载体基数为偶数；奇数载体必有固定边界。

## 第 1A 层：静态再进入

### P1A.1 — 两状态静态不可能性
**本仓库已证明**：`TwoState.no_static_self_reference`。

### P1A.2 — 一个自对偶扩展
**本仓库已证明**：三状态模型恰有一个静态固定点。

### P1A.3 — 一般边界分解
Core 中已有基础分解；更强的有限分解 theorem 仍是可选后续目标，不属于 v1.0 必要范围。

## 第 1B 层：动态再进入

### P1B.1 — 精确二周期
**本仓库已证明**：两状态 crossing 两步返回原状态。

### P1B.2 — 非一周期
**本仓库已证明**：一步 crossing 必改变状态。

## 第 2 层：序理论自指

### P2.1 — 固定点存在
**外部已有**：Knaster–Tarski；本仓库在 `OrderTheoretic` 中实例化。

### P2.2 — 最小 / 最大自指状态
**外部已有**：由 Mathlib 固定点结构直接得到，本仓库只做桥接。

## 第 3 层：逻辑桥

### P3.1 — primary algebra bridge
**部分完成**：`PrimaryBoolean` 已给出 raw syntax 与 false / OR / NOT 表达式之间的双向翻译和布尔语义保持。

完整 primary-algebra quotient / equational theory 与 Schwartz 的 derivability-preserving equivalence 不属于冻结的 v1.0 scope。

### P3.2 — Varela / Kleene 三值桥
**部分完成**：`KleeneThree` 已形式化 Strong Kleene 三值、connectives、Boolean embedding、De Morgan，并证明三状态 crossing 与 K3 negation 的精确对应。

完整 Varela syntax 与 Schwartz derivability bridge 不属于 v1.0 scope。

### P3.3 — Boolean → K3 保守语义桥
**本仓库已证明**：对布尔赋值，K3 evaluation 恰是布尔 evaluation 的嵌入；对任意 K3 赋值，位置 / 排中式公式恰在变量已确定时为真。

## 第 4 层：表示型 / 对角自指

### P4.1 — Lawvere bridge
**外部已有**：Mathlib 的 `Function.exists_fixed_point_of_surjective`，本仓库在 `Representational` 中实例化。

### P4.2 — 无固定点对全表示的障碍
**本仓库已证明**：结果类型存在无固定点 endomap 时，不可能有对应的全满射 Lawvere 表示。

### P4.3 — 最小对角表示条件
**本仓库已证明**：不需要全满射；只要表示某个 endomap 对应的关键 self-applied diagonal，就足以迫出固定点。partial representation 本身可以与 fixed-point-free crossing 共存。

P6.23 又把这个边界推广到 partial / guarded self-application。更进一步的 typed/modal/effectful strengthening 已延期到 v1.0 之后。

## 第 5 层：可计算自指

### P5.1 — Kleene bridge
**外部已有**：Mathlib 已形式化 Rogers fixed point 与 Kleene second recursion theorem，本仓库在 `Computability` 中显式桥接。

从 generic representation / re-entry 到 program-code self-reference 的更强统一桥仍是可选 post-v1.0 方向。

## 第 6 层：逐步增加条件的行动者框架

### P6.1 — 未来可区分性 / 有限表示
**本仓库已证明**：历史未来等价由所有 continuation 决定；canonical quotient 与 Myhill–Nerode 正则性相连。

### P6.2 — 用 bisimulation 表示持续同一性
**本仓库已证明**：bisimilarity 是单调 one-step operator 的最大固定点，并有共归纳原理；labelled 版本与 future equivalence 接通。

### P6.3 — 行动下的 viability
**本仓库已证明**：safe predecessor 的最大固定点就是 viability kernel；viable state 必安全且能选择保持 viable 的行动。

### P6.4 — 局部 / 全局障碍
**本仓库已证明**：局部可满足甚至两两相容，都不必推出全局 witness。

### P6.5 — 有限嵌套 gluing
**本仓库已证明**：有限非空嵌套约束中，局部可满足即可推出全局可满足。

### P6.6 — 重叠相容 gluing
**本仓库已证明**：cover + overlap agreement 足以拼接出 global assignment，不要求嵌套。

### P6.7 — 信息 refinement 与 garbling
**本仓库已证明**：确定性 refinement 与 Markov garbling 都满足“后处理不能创造信息”的方向；并连接 Bayes risk 与 KL data processing。

### P6.8 — 信息 / 未来区分桥
**本仓库已证明**：经 residual-language 因子化的表示保持 future equivalence。

### P6.9 — 信息损失 / 控制能力桥
**本仓库已证明**：适当的 dynamics commuting 与 safety preservation / reflection 控制 viability / recovery 的保持和反射。

### P6.10 — 定向控制模拟
**本仓库已证明**：前向与后向 simulation 分别承担能力保持与能力反射。

### P6.11 — 安全信息充分性
**本仓库已证明**：safety label 在 abstraction fiber 上不变，当且仅当 safety 可经 abstraction 因子化。

### P6.12 — 控制条件消融
**本仓库已证明**：前向 simulation、安全保持、后向 simulation、安全反射都各有独立删除反例。

### P6.13 — 目的相对能力
**本仓库已证明**：相同 dynamics 配不同 action-relevant purpose 可以得到不同 viability kernel；放宽 purpose 对 viability / recovery 单调。

### P6.14 — observation-relative local sufficiency
**本仓库已证明**：所需 commitment 可经 observation 因子化，当且仅当不存在“同观测、不同所需 commitment”的 ambiguity witness。

### P6.15 — compositional / conditional sufficiency
**本仓库已证明**：local sufficiency + technical coverage + overlap compatibility 可构造 global commitment；再加 recoverability 可得到 conditional-composition witness。

### P6.16 — corrigibility / reopening
**本仓库已证明**：失配检测、revision、false-alarm rejection、recovery 与 continuity 被分开建模，并给出依赖图和 ablation countermodel。

### P6.17 — guarded recursive self-improvement scaffold
**本仓库已证明**：把 self-modification、verifier soundness / migration、invariant、capability monotonicity 与 reality tracking 组合成 guarded RSI scaffold。这里的保证依赖显式假设，不等于 open-ended RSI 已被证明。

### P6.18 — certified expansion、资源与长期结构
**本仓库已证明**：独立 sound certificate authority 可以安全扩大 acceptance domain；验证资源、strict growth 与长期 stabilization 分别建模并给出可实现性 witness。

### P6.19 — explicit trusted kernel、proof cost 与有限增长界
**本仓库已证明**：显式 proof object 与小 checker 支持 sound expansion；proof-check cost 与 callability 分离；有限 capability universe 对连续严格增长给出全局长度界。

### P6.20 — 版本复现诊断、可持续 callability、kernel migration、联合收敛
**本仓库已证明**：完整版本 recurrence 在 non-degradation 下意味着 capability plateau；bounded proof witnesses 与预算可保证长期 callability；predecessor-checked kernel handoff 传播 trust invariant；capability / trust / reality 的最终稳定可组合。

### P6.21 — 变延迟、内生资源、trust delegation、无限 capability order
**本仓库已证明**：eventually fresh schedule 处理变延迟 / 乱序；内生资源可持续性、compromise-aware trust delegation、无限 capability chain 与第一版 invariant role core 均被分开形式化。

### P6.22 — 精确调度、资源 viability、threshold trust、ranked growth、完整 RSI core
**本仓库已证明**：

- eventual freshness 与“保持所有 eventually-stable Boolean requirement”精确等价；
- verification resource sustainability 是一个 viability kernel；
- threshold quorum 在 bounded compromise 下给出 sound handoff；
- 良基 rank 排除 infinite strict capability growth；
- 两种 RSI condition language 可翻译到共同六角色 core。

### P6.23 — self-certification barrier、changing evaluator、branch/archive、partial Lawvere
状态：**第一层形式结果已完成；具体元逻辑集成仍受 Foundation toolchain gate 限制。**

主要结果：

- universal self-certification 可以与 semantic unsoundness 共存；
- 有 non-circular grounded root 时可沿 semantic transfer 传播 soundness；
- changing evaluator 存在统一 strict transitive extension，当且仅当 local edge union 的 transitive closure 无环；
- 有限 state space 上这一条件等价于 Nat common potential；无限时不等价；
- selected branch 可以 recurrence / plateau，而 retained archive 继续严格增长；
- WQO 对 monotone antichain archive 有稳定结论，但不能阻止 recomputed Pareto frontier 永久替换；
- partial / guarded Lawvere 精确隔离了“self-application 是否有定义 / guard 是否打开”的阈值。

### P6.24 — 有限、延迟、噪声与版本化 evidence 下的 evaluator grounding
状态：**phase complete / formal layer closed。**

结果把 grounding 分成四条彼此独立的维度：

1. anchor 对当前 goal-relevant commitment 的语义充分性；
2. 对 anchor 的时间访问是否足够新鲜；
3. noisy / garbled observation 对决策问题是否信息充分；
4. evaluator migration 后 evidence provenance 是否仍有效。

还得到：

- least sufficient anchor 与有限 observation-cardinality lower bound；
- insufficient finite anchor 可以长期通过 proxy validation，同时 external goal 回退；
- history immutability 与 current qualification 分离；
- stale premise 沿 transitive dependency 使结论失效，independent anchor path 可存活。

### P6.25 — quantitative decision-relative grounding
**本仓库已证明**：定义 loss-scaled risk gap；证明 epsilon 单调性、零误差精确情况、garbling 方向、additive composition、family / uniform bounded-loss 版本，并有严格 Boolean 例子。

### P6.26 — sharp task-family scheduling
**本仓库已证明**：对给定 stable Boolean task family，schedule adequacy 有精确判据；取全部 stable Boolean task 时恰恢复 universal eventual freshness；singleton family 给出严格反例。

### P6.27 — evaluator morphism 与 proof-carrying provenance
**本仓库已证明**：

- `BridgeCertificate` 与 `EvaluatorMorphism` 的 identity / composition；
- same-state `VersionBridge`；
- evidence 与 transitive dependency transport；
- 两步 certificate composition；
- 只保持 external goal、不保持 evaluator judgment 的候选映射不足。

### P6.28 — grounded archive dynamics 与 progress layer separation
**本仓库已证明 / phase complete**。

严格分离五层：

1. archive set growth；
2. frontier replacement；
3. evaluator-relative frontier progress；
4. fixed external goal progress；
5. capability novelty。

同时给出把相邻层提升所需的 goal-soundness、capability-soundness、goal→capability reflection、dominance-complete frontier 等条件，并给出长期 stopping criteria。

### P6.29 — framework morphism 与 guide dependency core
**本仓库已证明**：`FrameworkMorphism`、`RSIFrameworkMorphisms`、`GuideCore`。

generic framework morphism 提供 condition / capability / realization map、derivation 与 satisfaction preservation、compatibility transport、identity / composition、sufficiency transport、reflection 条件、framework equivalence 和 morphism-induced invariant core。

guide 只形式化有明确数学含义的依赖标签：

- minimal self-reference；
- identity continuity；
- reality-changing agency；
- effective finitude；
- purpose；
- local-sufficiency problem；
- corrigibility 独立支路；
- local sufficiency + compatibility + recoverability 的 conditional composition。

并显式证明 effective finitude 不要求 finite state space。

## 元框架目标

### M1 — condition ablation
状态：**generic machinery 已形式化，且有具体实例。**

### M2 — minimal sufficient framework
状态：**generic machinery + selected instances 已证明。** 穷尽枚举不属于 v1.0 scope。

### M3 — incompatibility edge
状态：**generic machinery + 多个实例已证明。** 已有 representational conflict 与 RSI recurrence/growth conflict。

### M4 — feasible minimal sufficiency
状态：**已证明，并有多个具体实例。** 只有同时具备 capability sufficiency 和 semantic realizability 的 condition set 才作为可行 framework candidate。

### M5 — invariant core
状态：**general morphism layer 已证明，第一批 RSI core lift 完成。**

旧的手工 role-map core 已被 certified morphism image 精确恢复，因此 invariant-core claim 可以表述为在结构保持翻译下保留的内容，而不是事后给角色贴标签。

## 冻结边界

本文件仍保留若干历史 target，是为了记录研究轨迹，不表示 v1.0 之前必须继续扩展。

v1.0 mandatory scope 已经冻结。仍明确延期的主要方向包括：

- 完整 primary-algebra / Varela / Schwartz derivability formalization；
- Foundation toolchain 对齐后的具体 Löb / Gödel / Tarski integration；
- 没有得到更尖锐 threshold 的 typed/modal/effectful self-reference；
- 更完整的 rank-completeness、Byzantine quorum、general objective 等扩展。

这些方向只有在以后出现新的、可检查的 theorem 时才应重新进入主干。
