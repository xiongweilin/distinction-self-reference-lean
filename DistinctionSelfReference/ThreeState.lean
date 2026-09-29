import DistinctionSelfReference.Core

namespace DistinctionSelfReference
namespace ThreeState

/--
A minimal three-state extension with one self-dual boundary state.

This is a small independent model, not a claim that Varela's full calculus is
identical to this datatype.
-/
inductive State
  | unmarked
  | boundary
  | marked
  deriving DecidableEq, Repr

def cross : State → State
  | .unmarked => .marked
  | .boundary => .boundary
  | .marked => .unmarked

@[simp] theorem cross_unmarked : cross .unmarked = .marked := rfl
@[simp] theorem cross_boundary : cross .boundary = .boundary := rfl
@[simp] theorem cross_marked : cross .marked = .unmarked := rfl

theorem cross_involutive : Function.Involutive cross := by
  intro x
  cases x <;> rfl

def distinction : InvolutiveDistinction State where
  cross := cross
  involutive := cross_involutive

/-- The added boundary state is exactly the static fixed point. -/
theorem fixed_iff_boundary (x : State) :
    cross x = x ↔ x = .boundary := by
  cases x <;> simp [cross]

/-- The three-state model has exactly one static self-reference state. -/
theorem existsUnique_static_self_reference : ∃! x, cross x = x := by
  refine ⟨.boundary, rfl, ?_⟩
  intro y hy
  exact (fixed_iff_boundary y).mp hy

end ThreeState
end DistinctionSelfReference
