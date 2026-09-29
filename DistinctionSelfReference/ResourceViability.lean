import DistinctionSelfReference.Viability

namespace DistinctionSelfReference
namespace ResourceViability

open Viability

universe u

/--
A controlled verification-resource system. Cost is the resource required to
execute the current checking step; an action selects regeneration.
-/
structure ResourceSystem (Action : Type u) where
  cost : Nat → Nat
  regen : Nat → Action → Nat

namespace ResourceSystem

variable {Action : Type u}

/-- Endogenous next resource level after paying cost and applying regeneration. -/
def nextBudget
    (R : ResourceSystem Action)
    (budget : Nat)
    (action : Action) : Nat :=
  budget - R.cost budget + R.regen budget action

/-- A resource level is immediately callable when it covers the current cost. -/
def safeSet (R : ResourceSystem Action) : Set Nat :=
  {budget | R.cost budget ≤ budget}

/-- Resource dynamics as an ordinary controlled viability problem. -/
def controlled
    (R : ResourceSystem Action) :
    Viability.ControlledSystem Nat Action where
  step := R.nextBudget
  safe := R.safeSet

/-- Sustainable resource levels are exactly the viability kernel. -/
def sustainable
    (R : ResourceSystem Action) : Set Nat :=
  R.controlled.kernel

theorem mem_sustainable_iff
    (R : ResourceSystem Action)
    (budget : Nat) :
    budget ∈ R.sustainable ↔
      R.cost budget ≤ budget ∧
      ∃ action, R.nextBudget budget action ∈ R.sustainable := by
  exact R.controlled.mem_kernel_iff budget

/--
A lower resource floor B is viable when every budget above B can pay its cost
and choose an action whose regeneration is at least that cost.
-/
theorem floor_subset_sustainable
    (R : ResourceSystem Action)
    (B : Nat)
    (hcost : ∀ budget, B ≤ budget → R.cost budget ≤ budget)
    (hregen : ∀ budget, B ≤ budget →
      ∃ action, R.cost budget ≤ R.regen budget action) :
    {budget | B ≤ budget} ⊆ R.sustainable := by
  apply R.controlled.subset_kernel_of_postfixed
  intro budget hB
  constructor
  · exact hcost budget hB
  · rcases hregen budget hB with ⟨action, hregenAction⟩
    refine ⟨action, ?_⟩
    change B ≤ budget - R.cost budget + R.regen budget action
    have hcall := hcost budget hB
    calc
      B ≤ budget := hB
      _ = budget - R.cost budget + R.cost budget := by
        rw [Nat.sub_add_cancel hcall]
      _ ≤ budget - R.cost budget + R.regen budget action := by
        exact Nat.add_le_add_left hregenAction _

/-- Thus a single initial resource level above the invariant floor is sustainable. -/
theorem sustainable_of_floor
    (R : ResourceSystem Action)
    (B budget : Nat)
    (hcost : ∀ b, B ≤ b → R.cost b ≤ b)
    (hregen : ∀ b, B ≤ b →
      ∃ action, R.cost b ≤ R.regen b action)
    (hbudget : B ≤ budget) :
    budget ∈ R.sustainable :=
  floor_subset_sustainable R B hcost hregen hbudget

end ResourceSystem

namespace DepletingExample

/-- Fixed cost one, no regeneration, and no control choice. -/
def system : ResourceSystem Unit where
  cost := fun _ => 1
  regen := fun _ _ => 0

@[simp] theorem nextBudget (b : Nat) :
    system.nextBudget b Unit.unit = b - 1 :=
  rfl

/--
No finite budget is indefinitely sustainable when one unit is consumed at
every step and nothing regenerates.
-/
theorem sustainable_empty :
    system.sustainable = ∅ := by
  ext b
  constructor
  · intro hb
    induction b with
    | zero =>
        have hsafe := (system.mem_sustainable_iff 0).mp hb |>.1
        simp [system] at hsafe
    | succ n ih =>
        rcases (system.mem_sustainable_iff (n + 1)).mp hb with
          ⟨hsafe, action, hnext⟩
        cases action
        have hnext' : n ∈ system.sustainable := by
          simpa [system, ResourceSystem.nextBudget] using hnext
        exact ih hnext'
  · intro h
    simp at h

end DepletingExample
end ResourceViability
end DistinctionSelfReference
