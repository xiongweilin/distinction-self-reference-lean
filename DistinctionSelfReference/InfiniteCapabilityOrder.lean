import DistinctionSelfReference.FiniteCapabilityGrowth

namespace DistinctionSelfReference
namespace InfiniteCapabilityOrder

open CapabilityOrder
open CapabilityDynamics

universe u

/-- No infinite chain can strictly improve at every step. -/
def NoInfiniteStrictGrowth (Capability : Type u) : Prop :=
  ¬ ∃ chain : Nat → Profile Capability,
      ∀ n, StrictGrowth (chain n) (chain (n + 1))

/-- Finite capability universes admit no infinite everywhere-strict chain. -/
theorem finite_noInfiniteStrictGrowth
    (Capability : Type u)
    [Finite Capability] :
    NoInfiniteStrictGrowth Capability := by
  rintro ⟨chain, hstrict⟩
  rcases FiniteCapabilityGrowth.exists_nonStrict_before_succ_total chain with
    ⟨k, hk, hnot⟩
  exact hnot (hstrict k)

/-- Canonical growing profile over an infinite capability universe. -/
def natProfile (n : Nat) : Profile Nat where
  capabilities := {c | c < n}

theorem natProfile_strict (n : Nat) :
    StrictGrowth (natProfile n) (natProfile (n + 1)) := by
  have hle : natProfile n ≤ natProfile (n + 1) := by
    intro c hc
    change c < n at hc
    change c < n + 1
    omega
  have hne : natProfile n ≠ natProfile (n + 1) := by
    intro heq
    have hcaps := congrArg Profile.capabilities heq
    have hn : n ∈ (natProfile (n + 1)).capabilities := by
      change n < n + 1
      omega
    rw [← hcaps] at hn
    change n < n at hn
    omega
  exact lt_of_le_of_ne hle hne

/--
Infinite capability types can support genuinely open-ended strict capability
growth; finite cardinality bounds therefore do not generalize automatically.
-/
theorem nat_has_infinite_strictGrowth :
    ∃ chain : Nat → Profile Nat,
      ∀ n, StrictGrowth (chain n) (chain (n + 1)) :=
  ⟨natProfile, natProfile_strict⟩

theorem nat_not_noInfiniteStrictGrowth :
    ¬ NoInfiniteStrictGrowth Nat := by
  intro h
  exact h nat_has_infinite_strictGrowth

/--
A chain-condition hypothesis can replace finiteness when reasoning only needs
to exclude open-ended strict improvement.
-/
def SatisfiesAscendingChainCondition
    (Capability : Type u) : Prop :=
  NoInfiniteStrictGrowth Capability

theorem no_openEnded_growth_of_chainCondition
    {Capability : Type u}
    (hacc : SatisfiesAscendingChainCondition Capability)
    (chain : Nat → Profile Capability) :
    ¬ ∀ n, StrictGrowth (chain n) (chain (n + 1)) := by
  intro h
  exact hacc ⟨chain, h⟩

end InfiniteCapabilityOrder
end DistinctionSelfReference
