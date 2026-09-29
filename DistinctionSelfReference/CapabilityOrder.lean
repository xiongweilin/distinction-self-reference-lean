import Mathlib.Data.Set.Basic

namespace DistinctionSelfReference
namespace CapabilityOrder

universe u

/-- A version is observed here only through the capabilities it currently has. -/
structure Profile (Capability : Type u) where
  capabilities : Set Capability

namespace Profile

variable {Capability : Type u}

/-- Capability preorder: A is no more capable than B when every A capability is in B. -/
def AtMost (A B : Profile Capability) : Prop :=
  A.capabilities ⊆ B.capabilities

instance : LE (Profile Capability) where
  le := AtMost

theorem le_def (A B : Profile Capability) :
    A ≤ B ↔ A.capabilities ⊆ B.capabilities :=
  Iff.rfl

theorem le_refl (A : Profile Capability) : A ≤ A :=
  Set.Subset.rfl

theorem le_trans {A B C : Profile Capability}
    (hAB : A ≤ B) (hBC : B ≤ C) : A ≤ C :=
  Set.Subset.trans hAB hBC

theorem le_antisymm {A B : Profile Capability}
    (hAB : A ≤ B) (hBA : B ≤ A) : A = B := by
  cases A with
  | mk a =>
      cases B with
      | mk b =>
          simp only [AtMost] at hAB hBA
          have hab : a = b := Set.Subset.antisymm hAB hBA
          cases hab
          rfl

instance : PartialOrder (Profile Capability) where
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm

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
    exact ⟨le_refl A, le_refl A⟩

end Profile

/-- A sequence of versions is capability-monotone when every step is non-degrading. -/
def MonotoneChain {Capability : Type u}
    (chain : ℕ → Profile Capability) : Prop :=
  ∀ n, chain n ≤ chain (n + 1)

theorem chain_mono
    {Capability : Type u}
    {chain : ℕ → Profile Capability}
    (hchain : MonotoneChain chain) :
    Monotone chain := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact Profile.le_refl (chain m)
  | succ n hmn ih =>
      exact Profile.le_trans ih (hchain n)

end CapabilityOrder
end DistinctionSelfReference
