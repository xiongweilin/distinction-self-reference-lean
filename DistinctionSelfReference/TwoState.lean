import DistinctionSelfReference.Core

namespace DistinctionSelfReference
namespace TwoState

/-- The smallest concrete carrier with two distinguishable sides. -/
inductive Side
  | unmarked
  | marked
  deriving DecidableEq, Repr

/-- Crossing swaps the two sides. -/
def cross : Side → Side
  | .unmarked => .marked
  | .marked => .unmarked

@[simp] theorem cross_unmarked : cross .unmarked = .marked := rfl
@[simp] theorem cross_marked : cross .marked = .unmarked := rfl

theorem cross_involutive : Function.Involutive cross := by
  intro x
  cases x <;> rfl

def distinction : InvolutiveDistinction Side where
  cross := cross
  involutive := cross_involutive

/-- No side is unchanged by crossing. -/
theorem cross_ne_self (x : Side) : cross x ≠ x := by
  cases x <;> simp [cross]

/--
Static self-reference fails in the minimal two-state crossing model:
there is no x with cross x = x.
-/
theorem no_static_self_reference : ¬ ∃ x, cross x = x := by
  rintro ⟨x, hx⟩
  exact cross_ne_self x hx

/--
On a two-element carrier, crossing is the unique fixed-point-free endomap.

This is a useful minimality fact: once re-entry changes the side is required
for both states, there is no remaining freedom in the update rule.
-/
theorem eq_cross_of_fixedPointFree (f : Side → Side)
    (h : ∀ x, f x ≠ x) : f = cross := by
  funext x
  cases x with
  | unmarked =>
      cases hfx : f .unmarked with
      | unmarked => exact (h .unmarked hfx).elim
      | marked => rfl
  | marked =>
      cases hfx : f .marked with
      | unmarked => rfl
      | marked => exact (h .marked hfx).elim

end TwoState
end DistinctionSelfReference
