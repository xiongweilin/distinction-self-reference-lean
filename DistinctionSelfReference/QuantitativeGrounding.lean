import DistinctionSelfReference.StochasticAnchorGrounding

namespace DistinctionSelfReference
namespace QuantitativeGrounding

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open MarkovGarbling
open StochasticAnchorGrounding

universe u v w z

/--
A decision-relative Le Cam style risk-gap bound.

For one loss, `approx` is at most `ε` worse than `gold`, up to the
loss-dependent scale `C`.  This is deliberately the risk side of the
randomization criterion; it does not claim that a total-variation deficiency
has already been formalized.
-/
def RiskGapAtMost
    {Theta : Type u} {X : Type v} {Y : Type w} {Decision : Type z}
    [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Decision]
    (C ε : ℝ≥0∞)
    (loss : Theta → Decision → ℝ≥0∞)
    (approx : Kernel Theta X) (gold : Kernel Theta Y)
    (prior : Measure Theta) : Prop :=
  bayesRisk loss approx prior ≤ bayesRisk loss gold prior + C * ε

/-- Approximate grounding for one decision problem. -/
def ApproximatelyGrounded
    {Theta : Type u} {X : Type v} {Decision : Type z}
    [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace Decision]
    (C ε : ℝ≥0∞)
    (loss : Theta → Decision → ℝ≥0∞)
    (P : Kernel Theta X)
    (prior : Measure Theta) : Prop :=
  bayesRisk loss P prior ≤ C * ε

theorem riskGapAtMost_mono
    {Theta : Type u} {X : Type v} {Y : Type w} {Decision : Type z}
    [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Decision]
    {C ε ε' : ℝ≥0∞}
    {loss : Theta → Decision → ℝ≥0∞}
    {approx : Kernel Theta X} {gold : Kernel Theta Y}
    {prior : Measure Theta}
    (hε : ε ≤ ε')
    (h : RiskGapAtMost C ε loss approx gold prior) :
    RiskGapAtMost C ε' loss approx gold prior := by
  unfold RiskGapAtMost at h ⊢
  have hmul : C * ε ≤ C * ε' := by
    simpa [mul_comm] using (mul_le_mul_left hε C)
  exact h.trans (add_le_add_right hmul _)

theorem exact_simulation_has_zero_gap
    {Theta : Type u} {X : Type v} {Y : Type w} {Decision : Type z}
    [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Decision]
    (C : ℝ≥0∞)
    (loss : Theta → Decision → ℝ≥0∞)
    (approx : Kernel Theta X) (gold : Kernel Theta Y)
    (prior : Measure Theta)
    (hsim : GarblesTo approx gold) :
    RiskGapAtMost C 0 loss approx gold prior := by
  unfold RiskGapAtMost
  simpa using bayesRisk_mono_of_garblesTo loss approx gold prior hsim

theorem approximatelyGrounded_of_gap
    {Theta : Type u} {X : Type v} {Y : Type w} {Decision : Type z}
    [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Decision]
    (C ε : ℝ≥0∞)
    (loss : Theta → Decision → ℝ≥0∞)
    (approx : Kernel Theta X) (gold : Kernel Theta Y)
    (prior : Measure Theta)
    (hgap : RiskGapAtMost C ε loss approx gold prior)
    (hgold : DecisionGrounded loss gold prior) :
    ApproximatelyGrounded C ε loss approx prior := by
  unfold RiskGapAtMost at hgap
  unfold DecisionGrounded at hgold
  unfold ApproximatelyGrounded
  simpa [hgold] using hgap

/--
Further post-processing of the approximate experiment cannot create an
`ε`-grounding guarantee that the finer experiment lacked.

Equivalently: if a garbled experiment satisfies a given risk-gap bound, then
its pre-garbling source satisfies the same bound.
-/
theorem source_inherits_gap_bound_from_garbling
    {Theta : Type u} {X : Type v} {X' : Type w} {Y : Type z}
    {Decision : Type*}
    [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace X']
    [MeasurableSpace Y] [MeasurableSpace Decision]
    (C ε : ℝ≥0∞)
    (loss : Theta → Decision → ℝ≥0∞)
    (source : Kernel Theta X) (garbled : Kernel Theta X')
    (gold : Kernel Theta Y)
    (prior : Measure Theta)
    (hgarble : GarblesTo source garbled)
    (hgap : RiskGapAtMost C ε loss garbled gold prior) :
    RiskGapAtMost C ε loss source gold prior := by
  unfold RiskGapAtMost at hgap ⊢
  exact (bayesRisk_mono_of_garblesTo loss source garbled prior hgarble).trans hgap

/--
Decision-relative risk-gap bounds compose additively.
-/
theorem riskGapAtMost_trans
    {Theta : Type u} {X : Type v} {Y : Type w} {Z : Type z}
    {Decision : Type*}
    [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [MeasurableSpace Decision]
    (C ε δ : ℝ≥0∞)
    (loss : Theta → Decision → ℝ≥0∞)
    (A : Kernel Theta X) (B : Kernel Theta Y) (G : Kernel Theta Z)
    (prior : Measure Theta)
    (hAB : RiskGapAtMost C ε loss A B prior)
    (hBG : RiskGapAtMost C δ loss B G prior) :
    RiskGapAtMost C (ε + δ) loss A G prior := by
  unfold RiskGapAtMost at hAB hBG ⊢
  calc
    bayesRisk loss A prior
        ≤ bayesRisk loss B prior + C * ε := hAB
    _ ≤ (bayesRisk loss G prior + C * δ) + C * ε :=
      add_le_add hBG le_rfl
    _ = bayesRisk loss G prior + C * (ε + δ) := by
      simp [mul_add, add_assoc, add_comm]

/--
A task family is a set of losses.  A uniform family bound uses the same
`ε`, while allowing each loss to carry its own scale `C loss`.
-/
def FamilyRiskGapAtMost
    {Theta : Type u} {X : Type v} {Y : Type w} {Decision : Type z}
    [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Decision]
    (family : Set (Theta → Decision → ℝ≥0∞))
    (C : (Theta → Decision → ℝ≥0∞) → ℝ≥0∞)
    (ε : ℝ≥0∞)
    (approx : Kernel Theta X) (gold : Kernel Theta Y)
    (prior : Measure Theta) : Prop :=
  ∀ loss, loss ∈ family →
    RiskGapAtMost (C loss) ε loss approx gold prior

theorem familyGap_mono
    {Theta : Type u} {X : Type v} {Y : Type w} {Decision : Type z}
    [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Decision]
    {family : Set (Theta → Decision → ℝ≥0∞)}
    {C : (Theta → Decision → ℝ≥0∞) → ℝ≥0∞}
    {ε ε' : ℝ≥0∞}
    {approx : Kernel Theta X} {gold : Kernel Theta Y}
    {prior : Measure Theta}
    (hε : ε ≤ ε')
    (h : FamilyRiskGapAtMost family C ε approx gold prior) :
    FamilyRiskGapAtMost family C ε' approx gold prior := by
  intro loss hloss
  exact riskGapAtMost_mono hε (h loss hloss)

theorem familyGap_trans
    {Theta : Type u} {X : Type v} {Y : Type w} {Z : Type z}
    {Decision : Type*}
    [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [MeasurableSpace Decision]
    (family : Set (Theta → Decision → ℝ≥0∞))
    (C : (Theta → Decision → ℝ≥0∞) → ℝ≥0∞)
    (ε δ : ℝ≥0∞)
    (A : Kernel Theta X) (B : Kernel Theta Y) (G : Kernel Theta Z)
    (prior : Measure Theta)
    (hAB : FamilyRiskGapAtMost family C ε A B prior)
    (hBG : FamilyRiskGapAtMost family C δ B G prior) :
    FamilyRiskGapAtMost family C (ε + δ) A G prior := by
  intro loss hloss
  exact riskGapAtMost_trans (C loss) ε δ loss A B G prior
    (hAB loss hloss) (hBG loss hloss)

end QuantitativeGrounding
end DistinctionSelfReference
