import DistinctionSelfReference.AdvancedRSIDependencyGraph
import DistinctionSelfReference.NextRSIDependencyGraph

namespace DistinctionSelfReference
namespace FullRSIInvariantCore

inductive Role
  | selfModification
  | capabilityOrder
  | invariantPreservation
  | realityVerification
  | trustTransfer
  | resourceCallability
  deriving DecidableEq, Repr

def CoveredBy {Condition : Type}
    (map : Condition → Role)
    (conditions : Set Condition)
    (role : Role) : Prop :=
  ∃ c, c ∈ conditions ∧ map c = role

/--
A role-complete representative condition family drawn from the advanced RSI
language. Each member already occurs in one of its proved minimal components.
-/
def advancedConditions : Set AdvancedRSIDependencyGraph.Condition :=
  {c |
    c = .strictImprovement ∨
    c = .capabilityOrder ∨
    c = .trustedKernelSoundness ∨
    c = .exactRealityCorrection ∨
    c = .proofChecking ∨
    c = .sufficientBudget}

def advancedMap : AdvancedRSIDependencyGraph.Condition → Role
  | .strictImprovement => .selfModification
  | .capabilityOrder => .capabilityOrder
  | .oldVerifierSoundness => .invariantPreservation
  | .trustedKernelSoundness => .invariantPreservation
  | .exactRealityCorrection => .realityVerification
  | .requirementConvergence => .realityVerification
  | .proofChecking => .trustTransfer
  | .explicitProofObject => .trustTransfer
  | .proofCheckCostModel => .resourceCallability
  | .sufficientBudget => .resourceCallability
  | _ => .capabilityOrder

/--
A role-complete representative condition family drawn from the next-phase RSI
language.
-/
def nextConditions : Set NextRSIDependencyGraph.Condition :=
  {c |
    c = .fullVersionRecurrence ∨
    c = .pointwiseNonDegradation ∨
    c = .kernelTrustImpliesSoundness ∨
    c = .fixedLagRealityTracking ∨
    c = .predecessorCheckedMigration ∨
    c = .budgetCoverage}

def nextMap : NextRSIDependencyGraph.Condition → Role
  | .fullVersionRecurrence => .selfModification
  | .pointwiseNonDegradation => .capabilityOrder
  | .capabilityConvergence => .capabilityOrder
  | .initialKernelTrust => .invariantPreservation
  | .kernelTrustImpliesSoundness => .invariantPreservation
  | .requirementConvergence => .realityVerification
  | .fixedLagRealityTracking => .realityVerification
  | .predecessorCheckedMigration => .trustTransfer
  | .kernelVersionConvergence => .trustTransfer
  | .uniformProofCostBound => .resourceCallability
  | .budgetCoverage => .resourceCallability
  | .strictFirstCapabilityGrowth => .capabilityOrder

theorem advanced_covers_all (r : Role) :
    CoveredBy advancedMap advancedConditions r := by
  cases r with
  | selfModification =>
      refine ⟨.strictImprovement, ?_, rfl⟩
      exact Or.inl rfl
  | capabilityOrder =>
      refine ⟨.capabilityOrder, ?_, rfl⟩
      exact Or.inr (Or.inl rfl)
  | invariantPreservation =>
      refine ⟨.trustedKernelSoundness, ?_, rfl⟩
      exact Or.inr (Or.inr (Or.inl rfl))
  | realityVerification =>
      refine ⟨.exactRealityCorrection, ?_, rfl⟩
      exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | trustTransfer =>
      refine ⟨.proofChecking, ?_, rfl⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | resourceCallability =>
      refine ⟨.sufficientBudget, ?_, rfl⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

theorem next_covers_all (r : Role) :
    CoveredBy nextMap nextConditions r := by
  cases r with
  | selfModification =>
      refine ⟨.fullVersionRecurrence, ?_, rfl⟩
      exact Or.inl rfl
  | capabilityOrder =>
      refine ⟨.pointwiseNonDegradation, ?_, rfl⟩
      exact Or.inr (Or.inl rfl)
  | invariantPreservation =>
      refine ⟨.kernelTrustImpliesSoundness, ?_, rfl⟩
      exact Or.inr (Or.inr (Or.inl rfl))
  | realityVerification =>
      refine ⟨.fixedLagRealityTracking, ?_, rfl⟩
      exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | trustTransfer =>
      refine ⟨.predecessorCheckedMigration, ?_, rfl⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | resourceCallability =>
      refine ⟨.budgetCoverage, ?_, rfl⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

/--
Roles preserved by both independent RSI condition languages after semantic
translation.
-/
def fullCore : Set Role :=
  {r | CoveredBy advancedMap advancedConditions r ∧
       CoveredBy nextMap nextConditions r}

theorem fullCore_eq_univ :
    fullCore = Set.univ := by
  ext r
  constructor
  · intro h
    trivial
  · intro h
    exact ⟨advanced_covers_all r, next_covers_all r⟩

theorem every_role_in_fullCore (r : Role) :
    r ∈ fullCore := by
  rw [fullCore_eq_univ]
  trivial

end FullRSIInvariantCore
end DistinctionSelfReference
