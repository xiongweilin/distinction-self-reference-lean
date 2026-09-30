# 与区分和自指相关的已有结果

[English](Established.md) | [简体中文](Established.zh-CN.md)

本文专门区分“已有数学结果”和“本仓库自己的形式化实验”。

## 1. Spencer-Brown：区分、calling 与 crossing

George Spencer-Brown 的 *Laws of Form*（1969）从区分出发，发展 indications calculus。常见表述中，两条核心算术律称为 **law of calling** 与 **law of crossing**。

本仓库只做保守抽取：

- 在最小语义模型中，可以把 crossing 建模为一个对合操作；
- 这本身**不等于**完整形式化 primary arithmetic 或 primary algebra。

参考：

- G. Spencer-Brown, *Laws of Form*, 1969.
- Oxford Handbook 对 calling / crossing laws 的讨论：
  https://academic.oup.com/edited-volume/28359/chapter-abstract/215235298

## 2. Varela：自指与第三状态

Francisco Varela 1975 年的论文把 indications calculus 扩展到自指；其摘要明确讨论由 self-indication 出现的第三状态。

参考：

- F. J. Varela, “A Calculus for Self-Reference”, *International Journal of General Systems* 2(1), 1975, pp. 5–24.
  https://doi.org/10.1080/03081077508960828

范围说明：本仓库的三状态模型只是最小固定点实验，并不是 Varela calculus 的完整形式化。

## 3. Schwartz 的同构结果

Daniel G. Schwartz（1981）给出了到更标准逻辑记号的精确翻译 / 同构：

- Spencer-Brown primary algebra 被描述为与经典命题逻辑本质同构；
- Varela self-reference calculus 被同构翻译到 S. C. Kleene 的三值 partial-recursion logic 的一个公理化版本。

参考：

- D. G. Schwartz, “Isomorphisms of Spencer-Brown's Laws of Form and Varela's Calculus for Self-Reference”, *International Journal of General Systems* 6(4), 1981, pp. 239–255.
  https://doi.org/10.1080/03081078108934802

这为未来形式化提供了一个很重要的检验目标：如果继续编码 primary algebra 或 Varela calculus，应能检查是否真的捕捉了预期等式理论，而不只是语法外形。

## 4. Lawvere 固定点定理

Lawvere 的对角 / 固定点定理给出一个非常一般的机制：足够强的内部表示能力会迫使固定点出现。

Lean 中有两条直接可用路线：

- Mathlib 的 `Function.exists_fixed_point_of_surjective`，文档将它解释为类型 / 函数层面的 Lawvere fixed-point theorem 实例；
- Matthew Nestor 的 Lean 4 范畴论形式化：
  https://github.com/mdnestor/LawvereFixedPoint

`DistinctionSelfReference/Representational.lean` 直接复用 Mathlib 结果，不重复证明。

## 5. Knaster–Tarski 固定点定理

完备格上的单调自映射，其固定点组成完备格，因此存在最小和最大固定点。

Mathlib 已经提供：

- `Mathlib.Order.FixedPoints`
- `fixedPoints.completeLattice`
- `OrderHom.lfp` / `OrderHom.gfp`

`DistinctionSelfReference/OrderTheoretic.lean` 直接桥接这些已有结果。

## 6. Rogers 与 Kleene 的可计算固定点

Mathlib 在 `Mathlib.Computability.PartrecCode` 中已经形式化程序码层面的自指：

- `Nat.Partrec.Code.fixed_point`：Rogers fixed-point theorem；
- `Nat.Partrec.Code.fixed_point₂`：Kleene second recursion theorem。

这类定理说的是：对程序描述的可计算变换存在扩展意义 / 行为意义上的固定点。它们与下面几类结构不同：

- 字面状态固定点；
- 周期二轨道；
- 序理论最小固定点。

`DistinctionSelfReference/Computability.lean` 把这条分支作为独立框架显式暴露出来。

## 7. 本项目使用的工作分类

本项目暂时把已有自指机制区分为：

1. **状态固定点**：`x = f(x)`；
2. **动态复现 / 周期性**：`f^n(x) = x`；
3. **序理论固定点**：有结构偏序上的单调自映射；
4. **对角 / 表示型固定点**：Lawvere 风格自应用；
5. **可计算固定点**：Rogers / Kleene 的程序描述固定点；
6. **逻辑翻译桥**：区分演算与标准逻辑演算之间的同构或保守翻译。

本仓库研究的问题是：要从其中一类推进到另一类，究竟需要哪些附加条件；没有桥接证明时，不把这些机制混称为同一种“自指”。
