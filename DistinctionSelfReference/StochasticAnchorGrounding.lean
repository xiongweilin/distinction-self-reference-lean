import DistinctionSelfReference.MarkovGarbling

namespace DistinctionSelfReference
namespace StochasticAnchorGrounding

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open MarkovGarbling

universe u v w z

/--
For one fixed decision problem and prior, an experiment is exactly
decision-grounded when its Bayes risk is zero.
-/
def DecisionGrounded
    {Theta : Type u} {X : Type v} {Decision : Type z}
    [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace Decision]
    (loss : Theta → Decision → ℝ≥0∞)
    (P : Kernel Theta X)
    (prior : Measure Theta) : Prop :=
  bayesRisk loss P prior = 0

/--
Markov post-processing cannot create zero-risk grounding.
If the noisier/garbled anchor is sufficient for the decision problem, then the
finer pre-garbling anchor was already sufficient.
-/
theorem grounded_garbling_implies_grounded_source
    {Theta : Type u} {X : Type v} {Y : Type w} {Decision : Type z}
    [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Decision]
    (loss : Theta → Decision → ℝ≥0∞)
    (P : Kernel Theta X) (Q : Kernel Theta Y)
    (prior : Measure Theta)
    (hgarble : GarblesTo P Q)
    (hgrounded : DecisionGrounded loss Q prior) :
    DecisionGrounded loss P prior := by
  unfold DecisionGrounded at hgrounded ⊢
  have hle := bayesRisk_mono_of_garblesTo loss P Q prior hgarble
  rw [hgrounded] at hle
  exact le_antisymm hle bot_le

/--
Conversely, positive irreducible decision risk in the finer anchor survives
every further garbling: noise cannot repair an already insufficient signal.
-/
theorem positive_risk_persists_under_garbling
    {Theta : Type u} {X : Type v} {Y : Type w} {Decision : Type z}
    [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Decision]
    (loss : Theta → Decision → ℝ≥0∞)
    (P : Kernel Theta X) (Q : Kernel Theta Y)
    (prior : Measure Theta)
    (hgarble : GarblesTo P Q)
    (hpositive : 0 < bayesRisk loss P prior) :
    0 < bayesRisk loss Q prior := by
  exact lt_of_lt_of_le hpositive
    (bayesRisk_mono_of_garblesTo loss P Q prior hgarble)

/--
A garbled anchor that is decision-grounded is therefore not evidence that
noise added useful external information; its zero-risk capability must already
have been present before post-processing.
-/
theorem garbling_cannot_create_decision_grounding
    {Theta : Type u} {X : Type v} {Y : Type w} {Decision : Type z}
    [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Decision]
    (loss : Theta → Decision → ℝ≥0∞)
    (P : Kernel Theta X) (Q : Kernel Theta Y)
    (prior : Measure Theta)
    (hgarble : GarblesTo P Q) :
    DecisionGrounded loss Q prior →
      DecisionGrounded loss P prior :=
  grounded_garbling_implies_grounded_source loss P Q prior hgarble

end StochasticAnchorGrounding
end DistinctionSelfReference
