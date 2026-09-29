import DistinctionSelfReference.Recovery

namespace DistinctionSelfReference
namespace RecoverySeparation

open Viability
open Recovery

/-- Two states are enough to separate recoverability from viability. -/
inductive State
  | outside
  | stable
  deriving DecidableEq, Repr

inductive Action
  | advance
  deriving DecidableEq, Repr

/--
The stable state is safe and remains stable. The outside state is unsafe but
one action moves it into the stable state.
-/
def system : ControlledSystem State Action where
  step
    | .outside, .advance => .stable
    | .stable, .advance => .stable
  safe
    | .outside => False
    | .stable => True

theorem stable_mem_kernel :
    State.stable ∈ system.kernel := by
  let X : Set State := { s | s = .stable }
  have hpost : X ⊆ system.viabilityStep X := by
    intro s hs
    change s = .stable at hs
    subst s
    exact ⟨True.intro, Action.advance, rfl⟩
  exact system.subset_kernel_of_postfixed X hpost rfl

theorem outside_not_mem_kernel :
    State.outside ∉ system.kernel := by
  intro h
  have hs := system.kernel_subset_safe h
  exact hs

theorem outside_recoverable :
    Recoverable system State.outside := by
  exact ⟨[Action.advance], stable_mem_kernel⟩

/--
Recoverability is strictly weaker than viability in general.
-/
theorem recoverable_not_imply_viable :
    ∃ (State Action : Type),
      ∃ C : ControlledSystem State Action,
        ∃ s, Recoverable C s ∧ s ∉ C.kernel := by
  exact ⟨State, Action, system, State.outside,
    outside_recoverable, outside_not_mem_kernel⟩

end RecoverySeparation
end DistinctionSelfReference
