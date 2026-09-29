import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Probability.Decision.Risk.RiskIncrease

namespace DistinctionSelfReference
namespace MarkovGarbling

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe u v w z

/--
Experiment Q is a garbling of experiment P when Q is obtained by
post-processing P with a Markov kernel.
-/
def GarblesTo
    {Theta : Type u} {X : Type v} {Y : Type w}
    [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace Y]
    (P : Kernel Theta X) (Q : Kernel Theta Y) : Prop :=
  ∃ eta : Kernel X Y, IsMarkovKernel eta ∧ Q = eta ∘ₖ P

/--
Garbling cannot reduce Bayes risk: the post-processed experiment cannot be
strictly more useful for a fixed decision problem merely by losing information.
-/
theorem bayesRisk_mono_of_garblesTo
    {Theta : Type u} {X : Type v} {Y : Type w} {Decision : Type z}
    [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Decision]
    (loss : Theta → Decision → ℝ≥0∞)
    (P : Kernel Theta X) (Q : Kernel Theta Y)
    (prior : Measure Theta)
    (h : GarblesTo P Q) :
    bayesRisk loss P prior ≤ bayesRisk loss Q prior := by
  rcases h with ⟨eta, heta, rfl⟩
  letI : IsMarkovKernel eta := heta
  exact bayesRisk_le_bayesRisk_comp loss P prior eta

/--
Risk-increase information cannot grow under Markov post-processing.
-/
theorem riskIncrease_mono_of_garblesTo
    {Theta : Type u} {X : Type v} {Y : Type w} {Decision : Type z}
    [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Decision]
    (loss : Theta → Decision → ℝ≥0∞)
    (P : Kernel Theta X) (Q : Kernel Theta Y)
    (prior : Measure Theta)
    (h : GarblesTo P Q) :
    riskIncrease loss Q prior ≤ riskIncrease loss P prior := by
  rcases h with ⟨eta, heta, rfl⟩
  letI : IsMarkovKernel eta := heta
  exact riskIncrease_comp_le loss P prior eta

/--
At the measure level, the same post-processing principle is witnessed by
the KL-divergence data-processing inequality.
-/
theorem klDiv_postprocessing_le
    {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y]
    (mu nu : Measure X) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (kappa : Kernel X Y) [IsMarkovKernel kappa] :
    klDiv (kappa ∘ₘ mu) (kappa ∘ₘ nu) ≤ klDiv mu nu :=
  klDiv_comp_right_le mu nu kappa

end MarkovGarbling
end DistinctionSelfReference
