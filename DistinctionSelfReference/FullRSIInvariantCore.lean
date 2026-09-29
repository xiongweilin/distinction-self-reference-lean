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

def advancedConditions : Set AdvancedRSIDependencyGraph.Condition :=
  AdvancedRSIDependencyGraph.required
      AdvancedRSIDependencyGraph.Capability.finiteStrictGrowthBound ∪
  AdvancedRSIDependencyGraph.required
      AdvancedRSIDependencyGraph.Capability.proofBoundedCallableExpansion ∪
  AdvancedRSIDependencyGraph.required
      AdvancedRSIDependencyGraph.Capability.realityConvergence

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

def nextConditions : Set NextRSIDependencyGraph.Condition :=
  NextRSIDependencyGraph.required
      NextRSIDependencyGraph.Capability.recurrentPlateauDiagnostic ∪
  NextRSIDependencyGraph.required
      NextRSIDependencyGraph.Capability.indefiniteCallability ∪
  NextRSIDependencyGraph.required
      NextRSIDependencyGraph.Capability.trustedKernelMigration ∪
  NextRSIDependencyGraph.required
      NextRSIDependencyGraph.Capability.jointTrustCapabilityRealityStability

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
      exact ⟨AdvancedRSIDependencyGraph.Condition.strictImprovement,
        by simp [advancedConditions, AdvancedRSIDependencyGraph.required], rfl⟩
  | capabilityOrder =>
      exact ⟨AdvancedRSIDependencyGraph.Condition.capabilityOrder,
        by simp [advancedConditions, AdvancedRSIDependencyGraph.required], rfl⟩
  | invariantPreservation =>
      exact ⟨AdvancedRSIDependencyGraph.Condition.trustedKernelSoundness,
        by simp [advancedConditions, AdvancedRSIDependencyGraph.required], rfl⟩
  | realityVerification =>
      exact ⟨AdvancedRSIDependencyGraph.Condition.exactRealityCorrection,
        by simp [advancedConditions, AdvancedRSIDependencyGraph.required], rfl⟩
  | trustTransfer =>
      exact ⟨AdvancedRSIDependencyGraph.Condition.proofChecking,
        by simp [advancedConditions, AdvancedRSIDependencyGraph.required], rfl⟩
  | resourceCallability =>
      exact ⟨AdvancedRSIDependencyGraph.Condition.sufficientBudget,
        by simp [advancedConditions, AdvancedRSIDependencyGraph.required], rfl⟩

theorem next_covers_all (r : Role) :
    CoveredBy nextMap nextConditions r := by
  cases r with
  | selfModification =>
      exact ⟨NextRSIDependencyGraph.Condition.fullVersionRecurrence,
        by simp [nextConditions, NextRSIDependencyGraph.required], rfl⟩
  | capabilityOrder =>
      exact ⟨NextRSIDependencyGraph.Condition.pointwiseNonDegradation,
        by simp [nextConditions, NextRSIDependencyGraph.required], rfl⟩
  | invariantPreservation =>
      exact ⟨NextRSIDependencyGraph.Condition.kernelTrustImpliesSoundness,
        by simp [nextConditions, NextRSIDependencyGraph.required], rfl⟩
  | realityVerification =>
      exact ⟨NextRSIDependencyGraph.Condition.fixedLagRealityTracking,
        by simp [nextConditions, NextRSIDependencyGraph.required], rfl⟩
  | trustTransfer =>
      exact ⟨NextRSIDependencyGraph.Condition.predecessorCheckedMigration,
        by simp [nextConditions, NextRSIDependencyGraph.required], rfl⟩
  | resourceCallability =>
      exact ⟨NextRSIDependencyGraph.Condition.budgetCoverage,
        by simp [nextConditions, NextRSIDependencyGraph.required], rfl⟩

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
