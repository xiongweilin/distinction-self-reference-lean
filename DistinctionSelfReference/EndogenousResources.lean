import DistinctionSelfReference.TrustedKernel

namespace DistinctionSelfReference
namespace EndogenousResources

open SelfModification
open TrustedKernel

/--
A time-indexed verification resource process.
Checking consumes cost, regeneration restores budget, and the next budget is
computed from the current one.
-/
structure Process where
  budget : Nat → Nat
  cost : Nat → Nat
  regen : Nat → Nat
  evolves :
    ∀ n, budget (n + 1) = budget n - cost n + regen n

namespace Process

/-- Every step remains executable under its endogenous budget. -/
def CallableForever (P : Process) : Prop :=
  ∀ n, P.cost n ≤ P.budget n

/--
If every step cost is bounded by B, the initial budget covers B, and each
step regenerates at least what it spends, then callability is sustainable
forever.
-/
theorem callableForever_of_self_sustaining
    (P : Process)
    (B : Nat)
    (hcost : ∀ n, P.cost n ≤ B)
    (hinit : B ≤ P.budget 0)
    (hregen : ∀ n, P.cost n ≤ P.regen n) :
    P.CallableForever := by
  have hbudget : ∀ n, B ≤ P.budget n := by
    intro n
    induction n with
    | zero => exact hinit
    | succ n ih =>
        have hcall : P.cost n ≤ P.budget n :=
          le_trans (hcost n) ih
        calc
          B ≤ P.budget n := ih
          _ = P.budget n - P.cost n + P.cost n := by
            rw [Nat.sub_add_cancel hcall]
          _ ≤ P.budget n - P.cost n + P.regen n := by
            exact Nat.add_le_add_left (hregen n) _
          _ = P.budget (n + 1) := by
            symm
            exact P.evolves n
  intro n
  exact le_trans (hcost n) (hbudget n)

/-- A permanently nondecreasing budget is a special sustainable case. -/
theorem callableForever_of_budget_floor
    (P : Process)
    (B : Nat)
    (hcost : ∀ n, P.cost n ≤ B)
    (hfloor : ∀ n, B ≤ P.budget n) :
    P.CallableForever := by
  intro n
  exact le_trans (hcost n) (hfloor n)

end Process

namespace DepletionExample

/-- One unit is initially available, checking costs one, and nothing regenerates. -/
def process : Process where
  budget
    | 0 => 1
    | _ + 1 => 0
  cost := fun _ => 1
  regen := fun _ => 0
  evolves := by
    intro n
    cases n <;> rfl

def kernel : Kernel Nat where
  Proof := Unit
  check := fun _ _ => true

def proposals (n : Nat) : Proposal Nat where
  before := n
  after := n + 1

theorem every_step_certified (n : Nat) :
    kernel.Certified (proposals n) :=
  ⟨Unit.unit, rfl⟩

/--
Certification at every step does not imply sustainable execution when the
verification resource is consumed faster than it regenerates.
-/
theorem not_callable_forever :
    ¬ process.CallableForever := by
  intro h
  have h1 := h 1
  simp [Process.CallableForever, process] at h1

end DepletionExample
end EndogenousResources
end DistinctionSelfReference
