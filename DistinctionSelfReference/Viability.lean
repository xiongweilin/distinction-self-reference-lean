import Mathlib.Order.FixedPoints

namespace DistinctionSelfReference
namespace Viability

universe u v

/--
A deterministic controlled system with a set of currently acceptable states.
-/
structure ControlledSystem (State : Type u) (Action : Type v) where
  step : State → Action → State
  safe : Set State

namespace ControlledSystem

variable {State : Type u} {Action : Type v}

/--
One-step viability transformer: a state is retained when it is safe and there
exists an action whose successor remains in the candidate set.
-/
def viabilityStep (C : ControlledSystem State Action) (X : Set State) : Set State :=
  { s | s ∈ C.safe ∧ ∃ a, C.step s a ∈ X }

theorem viabilityStep_mono (C : ControlledSystem State Action) :
    Monotone C.viabilityStep := by
  intro X Y hXY s hs
  rcases hs with ⟨hsafe, a, ha⟩
  exact ⟨hsafe, a, hXY ha⟩

def viabilityOperator (C : ControlledSystem State Action) :
    Set State →o Set State where
  toFun := C.viabilityStep
  monotone' := C.viabilityStep_mono

/--
The viability kernel is the greatest fixed point of the safe-predecessor
operator.
-/
def kernel (C : ControlledSystem State Action) : Set State :=
  C.viabilityOperator.gfp

theorem kernel_fixed (C : ControlledSystem State Action) :
    C.viabilityStep C.kernel = C.kernel :=
  C.viabilityOperator.isFixedPt_gfp

theorem mem_kernel_iff
    (C : ControlledSystem State Action) (s : State) :
    s ∈ C.kernel ↔
      s ∈ C.safe ∧ ∃ a, C.step s a ∈ C.kernel := by
  change s ∈ C.viabilityOperator.gfp ↔
    s ∈ C.viabilityOperator C.viabilityOperator.gfp
  rw [C.viabilityOperator.isFixedPt_gfp]

theorem kernel_subset_safe (C : ControlledSystem State Action) :
    C.kernel ⊆ C.safe := by
  intro s hs
  exact (C.mem_kernel_iff s).mp hs |>.1

theorem viable_has_viable_action
    (C : ControlledSystem State Action) {s : State}
    (hs : s ∈ C.kernel) :
    ∃ a, C.step s a ∈ C.kernel := by
  exact (C.mem_kernel_iff s).mp hs |>.2

/--
Coinduction principle for viability: any set whose members are safe and can
choose a successor inside the same set is contained in the viability kernel.
-/
theorem subset_kernel_of_postfixed
    (C : ControlledSystem State Action) (X : Set State)
    (hX : X ⊆ C.viabilityStep X) :
    X ⊆ C.kernel :=
  C.viabilityOperator.le_gfp hX

end ControlledSystem
end Viability
end DistinctionSelfReference
