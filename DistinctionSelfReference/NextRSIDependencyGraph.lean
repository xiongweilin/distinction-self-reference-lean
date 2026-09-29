import DistinctionSelfReference.MetaFramework

namespace DistinctionSelfReference
namespace NextRSIDependencyGraph

open MetaFramework

inductive Condition
  | pointwiseNonDegradation
  | fullVersionRecurrence
  | strictFirstCapabilityGrowth
  | uniformProofCostBound
  | budgetCoverage
  | predecessorCheckedMigration
  | initialKernelTrust
  | kernelTrustImpliesSoundness
  | capabilityConvergence
  | kernelVersionConvergence
  | requirementConvergence
  | fixedLagRealityTracking
  deriving DecidableEq, Repr

inductive Capability
  | recurrentPlateauDiagnostic
  | indefiniteCallability
  | trustedKernelMigration
  | jointTrustCapabilityRealityStability
  deriving DecidableEq, Repr

def required : Capability → Set Condition
  | .recurrentPlateauDiagnostic =>
      { .pointwiseNonDegradation, .fullVersionRecurrence }
  | .indefiniteCallability =>
      { .uniformProofCostBound, .budgetCoverage }
  | .trustedKernelMigration =>
      { .predecessorCheckedMigration, .initialKernelTrust,
        .kernelTrustImpliesSoundness }
  | .jointTrustCapabilityRealityStability =>
      { .capabilityConvergence, .kernelVersionConvergence,
        .requirementConvergence, .fixedLagRealityTracking }

def graph : FrameworkGraph Condition Capability where
  derives conditions cap := required cap ⊆ conditions
  monotone := by
    intro A B cap hAB hreq
    exact Set.Subset.trans hreq hAB

theorem required_minimal (cap : Capability) :
    graph.InclusionMinimal (required cap) {cap} := by
  constructor
  · intro t ht
    change t = cap at ht
    subst t
    exact Set.Subset.rfl
  · intro smaller hsmall hsuff
    have hreq := hsuff (t := cap) (by rfl)
    change required cap ⊆ smaller at hreq
    rw [Set.ssubset_iff_subset_ne] at hsmall
    exact hsmall.2 (Set.Subset.antisymm hsmall.1 hreq)

theorem recurrentPlateau_minimal :
    graph.InclusionMinimal
      (required Capability.recurrentPlateauDiagnostic)
      {Capability.recurrentPlateauDiagnostic} :=
  required_minimal Capability.recurrentPlateauDiagnostic

theorem indefiniteCallability_minimal :
    graph.InclusionMinimal
      (required Capability.indefiniteCallability)
      {Capability.indefiniteCallability} :=
  required_minimal Capability.indefiniteCallability

theorem trustedKernelMigration_minimal :
    graph.InclusionMinimal
      (required Capability.trustedKernelMigration)
      {Capability.trustedKernelMigration} :=
  required_minimal Capability.trustedKernelMigration

theorem jointStability_minimal :
    graph.InclusionMinimal
      (required Capability.jointTrustCapabilityRealityStability)
      {Capability.jointTrustCapabilityRealityStability} :=
  required_minimal Capability.jointTrustCapabilityRealityStability

end NextRSIDependencyGraph
end DistinctionSelfReference
