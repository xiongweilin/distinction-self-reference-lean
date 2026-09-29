import DistinctionSelfReference.KernelVerificationResources

namespace DistinctionSelfReference
namespace IndefiniteCallability

open SelfModification
open TrustedKernel
open KernelVerificationResources

universe u v

variable {Version : Type u}

/-- Every proposal in a sequence is callable under its time-indexed budget. -/
def CallableForever
    (K : Kernel.{u, v} Version)
    (C : CostModel K)
    (budget : Nat → Nat)
    (proposals : Nat → Proposal Version) : Prop :=
  ∀ n, CertifiedCallable K C (budget n) (proposals n)

/-- Callability may also be required only after a finite startup phase. -/
def EventuallyCallable
    (K : Kernel.{u, v} Version)
    (C : CostModel K)
    (budget : Nat → Nat)
    (proposals : Nat → Proposal Version) : Prop :=
  ∃ N, ∀ n, N ≤ n →
    CertifiedCallable K C (budget n) (proposals n)

/-- A uniform proof-cost bound plus covering budgets gives indefinite callability. -/
theorem callableForever_of_uniform_bound
    (K : Kernel.{u, v} Version)
    (C : CostModel K)
    (budget : Nat → Nat)
    (proposals : Nat → Proposal Version)
    (bound : Nat)
    (hwitness : ∀ n, ∃ proof,
      K.check (proposals n) proof = true ∧ C.cost (proposals n) proof ≤ bound)
    (hbudget : ∀ n, bound ≤ budget n) :
    CallableForever K C budget proposals := by
  intro n
  rcases hwitness n with ⟨proof, hcheck, hcost⟩
  exact ⟨proof, hcheck, le_trans hcost (hbudget n)⟩

/-- Eventual bounded checking cost and sufficient budgets imply eventual callability. -/
theorem eventuallyCallable_of_eventual_budget
    (K : Kernel.{u, v} Version)
    (C : CostModel K)
    (budget : Nat → Nat)
    (proposals : Nat → Proposal Version)
    (bound N : Nat)
    (hwitness : ∀ n, N ≤ n → ∃ proof,
      K.check (proposals n) proof = true ∧ C.cost (proposals n) proof ≤ bound)
    (hbudget : ∀ n, N ≤ n → bound ≤ budget n) :
    EventuallyCallable K C budget proposals := by
  refine ⟨N, ?_⟩
  intro n hn
  rcases hwitness n hn with ⟨proof, hcheck, hcost⟩
  exact ⟨proof, hcheck, le_trans hcost (hbudget n hn)⟩

/-- Pointwise budget enlargement preserves indefinite callability. -/
theorem callableForever_mono_budget
    (K : Kernel.{u, v} Version)
    (C : CostModel K)
    {small large : Nat → Nat}
    (hbudget : ∀ n, small n ≤ large n)
    (proposals : Nat → Proposal Version)
    (h : CallableForever K C small proposals) :
    CallableForever K C large proposals := by
  intro n
  exact callable_mono_budget K C (hbudget n) (h n)

namespace Example

def kernel : Kernel Nat where
  Proof := Unit
  check := fun _ _ => true

def cost : CostModel kernel where
  cost := fun p _ => p.after

def proposals (n : Nat) : Proposal Nat where
  before := n
  after := n + 1

def zeroBudget (_ : Nat) : Nat := 0

theorem each_certified (n : Nat) :
    kernel.Certified (proposals n) :=
  ⟨Unit.unit, rfl⟩

theorem never_callable_zero_budget (n : Nat) :
    ¬ CertifiedCallable kernel cost (zeroBudget n) (proposals n) := by
  apply not_callable_if_all_checked_proofs_over_budget
  intro proof _
  cases proof
  simp [zeroBudget, cost, proposals]

theorem not_eventually_callable_zero_budget :
    ¬ EventuallyCallable kernel cost zeroBudget proposals := by
  rintro ⟨N, hN⟩
  exact never_callable_zero_budget N (hN N le_rfl)

end Example
end IndefiniteCallability
end DistinctionSelfReference
