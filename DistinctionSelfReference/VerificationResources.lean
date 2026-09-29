import DistinctionSelfReference.SelfModification

namespace DistinctionSelfReference
namespace VerificationResources

open SelfModification

universe u

variable {Version : Type u}

/-- Cost model for checking or justifying one proposed modification. -/
structure CostModel (Version : Type u) where
  cost : Proposal Version → Nat

/--
A proposal is callable under a budget only if it is accepted and its verification
cost fits the available budget.
-/
def Callable
    (V : Verifier Version)
    (C : CostModel Version)
    (budget : Nat)
    (p : Proposal Version) : Prop :=
  V.accepts p ∧ C.cost p ≤ budget

theorem callable_mono_budget
    (V : Verifier Version)
    (C : CostModel Version)
    {small large : Nat}
    (hbudget : small ≤ large)
    {p : Proposal Version}
    (h : Callable V C small p) :
    Callable V C large p :=
  ⟨h.1, le_trans h.2 hbudget⟩

theorem callable_preserves_invariant
    (V : Verifier Version)
    (C : CostModel Version)
    (Invariant : Version → Prop)
    (hsound : V.SoundFor Invariant)
    {budget : Nat}
    {p : Proposal Version}
    (h : Callable V C budget p) :
    Invariant p.after :=
  hsound p h.1

/-- Verification acceptance alone does not imply practical callability. -/
theorem not_callable_of_over_budget
    (V : Verifier Version)
    (C : CostModel Version)
    {budget : Nat}
    {p : Proposal Version}
    (hover : budget < C.cost p) :
    ¬ Callable V C budget p := by
  intro h
  exact (Nat.not_le_of_gt hover) h.2

namespace Example

def verifier : Verifier Bool where
  accepts := fun _ => True

def costly : CostModel Bool where
  cost := fun _ => 2

def proposal : Proposal Bool where
  before := false
  after := true

theorem accepted : verifier.accepts proposal :=
  trivial

theorem not_callable_at_one :
    ¬ Callable verifier costly 1 proposal := by
  apply not_callable_of_over_budget
  decide

theorem callable_at_two :
    Callable verifier costly 2 proposal := by
  exact ⟨trivial, le_rfl⟩

end Example
end VerificationResources
end DistinctionSelfReference
