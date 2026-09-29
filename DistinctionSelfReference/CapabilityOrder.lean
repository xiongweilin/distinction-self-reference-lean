import Mathlib.Data.Set.Basic

namespace DistinctionSelfReference
namespace CapabilityOrder

universe u

/-- A version is observed here only through the capabilities it currently has. -/
structure Profile (Capability : Type u) where
  capabilities : Set Capability

namespace Profile

variable {Capability : Type u}

/-- Capability order: A is no more capable than B when every A capability is in B. -/
def AtMost (A B : Profile Capability) : Prop :=
  A.capabilities ⊆ B.capabilities

instance : PartialOrder (Profile Capability) where
  le := AtMost
  le_refl := by
    intro A
    exact Set.Subset.rfl
  le_trans := by
    intro A B C hAB hBC
    exact Set.Subset.trans hAB hBC
  le_antisymm := by
    intro A B hAB hBA
    cases A with
    | mk a =>
        cases B with
        | mk b =>
            change a ⊆ b at hAB
            change b ⊆ a at hBA
            have h : a = b := Set.Subset.antisymm hAB hBA
            cases h
            rfl

theorem le_def (A B : Profile Capability) :
    A ≤ B ↔ A.capabilities ⊆ B.capabilities :=
  Iff.rfl

/-- A strict capability improvement adds at least one capability and loses none. -/
def StrictlyImproves (A B : Profile Capability) : Prop :=
  A < B

/-- Capability equivalence in this extensional profile model is literal equality. -/
theorem capabilityEquivalent_iff_eq (A B : Profile Capability) :
    (A ≤ B ∧ B ≤ A) ↔ A = B := by
  constructor
  · rintro ⟨hAB, hBA⟩
    exact le_antisymm hAB hBA
  · intro h
    subst h
    exact ⟨le_rfl, le_rfl⟩

end Profile

/-- A sequence of versions is capability-monotone when every step is non-degrading. -/
def MonotoneChain {Capability : Type u}
    (chain : Nat → Profile Capability) : Prop :=
  ∀ n, chain n ≤ chain (n + 1)

theorem chain_mono
    {Capability : Type u}
    {chain : Nat → Profile Capability}
    (hchain : MonotoneChain chain) :
    Monotone chain := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih =>
      exact le_trans ih (hchain n)

end CapabilityOrder
end DistinctionSelfReference
