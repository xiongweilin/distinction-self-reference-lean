import DistinctionSelfReference.QuantitativeGrounding

namespace DistinctionSelfReference
namespace QuantitativeGrounding
namespace BinaryStrictnessExample

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open MarkovGarbling

/-- Zero-one loss for guessing a Boolean parameter. -/
def mismatchLoss (theta decision : Bool) : ℝ≥0∞ :=
  if theta = decision then 0 else 1

/-- Two equally weighted parameter points; normalization is unnecessary for strictness. -/
noncomputable def prior : Measure Bool :=
  Measure.dirac false + Measure.dirac true

theorem mismatchLoss_measurable :
    Measurable (Function.uncurry mismatchLoss) := by
  fun_prop

/-- Exact observation permits the identity estimator and hence zero Bayes risk. -/
theorem bayesRisk_exact_zero :
    bayesRisk mismatchLoss (Kernel.id : Kernel Bool Bool) prior = 0 := by
  apply le_antisymm
  · have h := bayesRisk_le_avgRisk mismatchLoss
      (Kernel.id : Kernel Bool Bool) (Kernel.id : Kernel Bool Bool) prior
    simpa [avgRisk, mismatchLoss, Kernel.id_apply] using h
  · exact bot_le

/-- With the observation discarded, either fixed Boolean decision incurs unit total loss. -/
theorem bayesRisk_discard_one :
    bayesRisk mismatchLoss (Kernel.discard Bool) prior = 1 := by
  rw [bayesRisk_discard mismatchLoss_measurable prior]
  rw [iInf_bool_eq]
  simp [prior, mismatchLoss, lintegral_add_measure]

/-- Complete observation loss is a genuine Markov garbling of the exact signal. -/
theorem exact_garblesTo_discard :
    GarblesTo (Kernel.id : Kernel Bool Bool) (Kernel.discard Bool) := by
  refine ⟨Kernel.discard Bool, inferInstance, ?_⟩
  simp

theorem discard_strictly_increases_bayesRisk :
    bayesRisk mismatchLoss (Kernel.id : Kernel Bool Bool) prior <
      bayesRisk mismatchLoss (Kernel.discard Bool) prior := by
  rw [bayesRisk_exact_zero, bayesRisk_discard_one]
  simp

/-- The discarded experiment cannot satisfy a zero-error gap against the exact experiment. -/
theorem discard_not_zero_gap :
    ¬ RiskGapAtMost 1 0 mismatchLoss
      (Kernel.discard Bool) (Kernel.id : Kernel Bool Bool) prior := by
  simp [RiskGapAtMost, bayesRisk_exact_zero, bayesRisk_discard_one]

/-- A unit-scale unit-error allowance is sufficient for this concrete loss. -/
theorem discard_has_unit_gap :
    RiskGapAtMost 1 1 mismatchLoss
      (Kernel.discard Bool) (Kernel.id : Kernel Bool Bool) prior := by
  simp [RiskGapAtMost, bayesRisk_exact_zero, bayesRisk_discard_one]

end BinaryStrictnessExample
end QuantitativeGrounding
end DistinctionSelfReference
