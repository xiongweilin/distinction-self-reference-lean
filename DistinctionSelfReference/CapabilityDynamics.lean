import Mathlib.Data.Set.Card
import DistinctionSelfReference.CapabilityOrder
import DistinctionSelfReference.SelfModification

namespace DistinctionSelfReference
namespace CapabilityDynamics

open CapabilityOrder
open SelfModification

universe u v

variable {Capability : Type u} {Payload : Type v}

/-- One step is a capability plateau when the extensional profiles are equal. -/
def Plateau
    (before after : Profile Capability) : Prop :=
  before = after

/-- One step is strict growth when the capability profile strictly increases. -/
def StrictGrowth
    (before after : Profile Capability) : Prop :=
  before < after

theorem plateau_or_strictGrowth
    (before after : Profile Capability)
    (hmono : before ≤ after) :
    Plateau before after ∨ StrictGrowth before after := by
  rcases eq_or_ne before after with h | h
  · exact Or.inl h
  · exact Or.inr (lt_of_le_of_ne hmono h)

/--
For a finite capability universe, strict capability growth strictly increases
the number of possessed capabilities.
-/
theorem ncard_lt_of_strictGrowth
    [Finite Capability]
    {before after : Profile Capability}
    (h : StrictGrowth before after) :
    before.capabilities.ncard < after.capabilities.ncard := by
  apply Set.ncard_lt_ncard
  · exact h
  · exact Set.toFinite after.capabilities

/-- No profile can contain more capabilities than exist in the finite universe. -/
theorem ncard_le_total
    [Finite Capability]
    (p : Profile Capability) :
    p.capabilities.ncard ≤ Nat.card Capability := by
  simpa [Set.ncard_univ] using
    Set.ncard_le_ncard (Set.subset_univ p.capabilities)

/--
Thus every strict step consumes positive finite cardinality headroom.
-/
theorem strictGrowth_bounded_by_total
    [Finite Capability]
    {before after : Profile Capability}
    (h : StrictGrowth before after) :
    before.capabilities.ncard < Nat.card Capability + 1 := by
  exact lt_of_lt_of_le
    (ncard_lt_of_strictGrowth h)
    (Nat.le_succ_of_le (ncard_le_total after))

/-- A modifier fixed point is stronger than a capability plateau. -/
def ModifierFixedPoint
    (M : Modifier (CapVersion Capability Payload))
    (v : CapVersion Capability Payload) : Prop :=
  M.propose v = v

theorem fixedPoint_implies_profile_plateau
    (M : Modifier (CapVersion Capability Payload))
    (v : CapVersion Capability Payload)
    (h : ModifierFixedPoint M v) :
    Plateau v.profile (M.propose v).profile := by
  simpa [Plateau] using (congrArg CapVersion.profile h).symm

/-
A capability plateau need not be a full version fixed point: payload may change
while the capability profile remains identical.
-/
namespace Example

def v0 : CapVersion Bool Bool where
  payload := false
  profile := ⟨{false}⟩

def v1 : CapVersion Bool Bool where
  payload := true
  profile := ⟨{false}⟩

theorem profile_plateau :
    Plateau v0.profile v1.profile :=
  rfl

theorem version_changes : v0 ≠ v1 := by
  intro h
  have hp := congrArg CapVersion.payload h
  change false = true at hp
  exact Bool.false_ne_true hp

end Example
end CapabilityDynamics
end DistinctionSelfReference
