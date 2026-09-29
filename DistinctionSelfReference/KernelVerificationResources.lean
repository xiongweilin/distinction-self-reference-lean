import DistinctionSelfReference.TrustedKernel

namespace DistinctionSelfReference
namespace KernelVerificationResources

open SelfModification
open TrustedKernel

universe u v

variable {Version : Type u}

/-- Cost of checking a particular proof object for a particular proposal. -/
structure CostModel
    (K : Kernel.{u, v} Version) where
  cost : (p : Proposal Version) → K.Proof → Nat

/--
A newly certified proposal is callable only when an explicit proof both checks
and fits the available proof-checking budget.
-/
def CertifiedCallable
    (K : Kernel.{u, v} Version)
    (C : CostModel K)
    (budget : Nat)
    (p : Proposal Version) : Prop :=
  ∃ proof, K.check p proof = true ∧ C.cost p proof ≤ budget

theorem callable_mono_budget
    (K : Kernel.{u, v} Version)
    (C : CostModel K)
    {small large : Nat}
    (hbudget : small ≤ large)
    {p : Proposal Version}
    (h : CertifiedCallable K C small p) :
    CertifiedCallable K C large p := by
  rcases h with ⟨proof, hcheck, hcost⟩
  exact ⟨proof, hcheck, le_trans hcost hbudget⟩

theorem callable_preserves_invariant
    (K : Kernel.{u, v} Version)
    (C : CostModel K)
    (Invariant : Version → Prop)
    (hsound : K.SoundFor Invariant)
    {budget : Nat}
    {p : Proposal Version}
    (h : CertifiedCallable K C budget p) :
    Invariant p.after := by
  rcases h with ⟨proof, hcheck, _⟩
  exact hsound p proof hcheck

/-- Every proof-bounded certified proposal is accepted by the expanded verifier. -/
theorem callable_implies_expanded_acceptance
    (old : Verifier Version)
    (K : Kernel.{u, v} Version)
    (C : CostModel K)
    {budget : Nat}
    {p : Proposal Version}
    (h : CertifiedCallable K C budget p) :
    (K.expandVerifier old).accepts p := by
  rcases h with ⟨proof, hcheck, _⟩
  exact K.accepts_checked old p proof hcheck

/--
Having a valid proof object is not enough for callability when every checking
witness exceeds the available budget.
-/
theorem not_callable_if_all_checked_proofs_over_budget
    (K : Kernel.{u, v} Version)
    (C : CostModel K)
    {budget : Nat}
    {p : Proposal Version}
    (hover : ∀ proof, K.check p proof = true → budget < C.cost p proof) :
    ¬ CertifiedCallable K C budget p := by
  rintro ⟨proof, hcheck, hcost⟩
  exact (Nat.not_le_of_gt (hover proof hcheck)) hcost

namespace Example

def kernel : Kernel Bool where
  Proof := Unit
  check p _ := p.after

def cost : CostModel kernel where
  cost := fun _ _ => 2

def proposal : Proposal Bool where
  before := false
  after := true

theorem checks :
    kernel.check proposal Unit.unit = true :=
  rfl

theorem not_callable_at_one :
    ¬ CertifiedCallable kernel cost 1 proposal := by
  apply not_callable_if_all_checked_proofs_over_budget
  intro proof _
  cases proof
  decide

theorem callable_at_two :
    CertifiedCallable kernel cost 2 proposal :=
  ⟨Unit.unit, checks, le_rfl⟩

end Example
end KernelVerificationResources
end DistinctionSelfReference
