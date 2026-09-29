import DistinctionSelfReference.MetaFramework

namespace DistinctionSelfReference
namespace AdvancedRSIDependencyGraph

open MetaFramework

/-- Conditions introduced after the first guarded-RSI scaffold. -/
inductive Condition
  | oldVerifierSoundness
  | certificateAuthoritySoundness
  | certificateChecking
  | capabilityOrder
  | strictImprovement
  | finiteCapabilityUniverse
  | verificationAcceptance
  | verificationCostModel
  | sufficientBudget
  | exactRealityCorrection
  | requirementConvergence
  | capabilityConvergence
  | explicitProofObject
  | trustedKernelSoundness
  | proofChecking
  | proofCheckCostModel
  deriving DecidableEq, Repr

inductive Capability
  | certifiedVerifierExpansion
  | strictCapabilityGrowth
  | boundedCallableUpgrade
  | realityConvergence
  | jointLongRunStability
  | proofCheckedVerifierExpansion
  | finiteStrictGrowthBound
  | proofBoundedCallableExpansion
  deriving DecidableEq, Repr

def required : Capability → Set Condition
  | .certifiedVerifierExpansion =>
      { .oldVerifierSoundness, .certificateAuthoritySoundness,
        .certificateChecking }
  | .strictCapabilityGrowth =>
      { .capabilityOrder, .strictImprovement }
  | .boundedCallableUpgrade =>
      { .verificationAcceptance, .verificationCostModel, .sufficientBudget }
  | .realityConvergence =>
      { .exactRealityCorrection, .requirementConvergence }
  | .jointLongRunStability =>
      { .exactRealityCorrection, .requirementConvergence,
        .capabilityConvergence }
  | .proofCheckedVerifierExpansion =>
      { .oldVerifierSoundness, .explicitProofObject,
        .trustedKernelSoundness, .proofChecking }
  | .finiteStrictGrowthBound =>
      { .capabilityOrder, .strictImprovement, .finiteCapabilityUniverse }
  | .proofBoundedCallableExpansion =>
      { .explicitProofObject, .trustedKernelSoundness, .proofChecking,
        .proofCheckCostModel, .sufficientBudget }

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

theorem certifiedExpansion_minimal :
    graph.InclusionMinimal
      (required Capability.certifiedVerifierExpansion)
      {Capability.certifiedVerifierExpansion} :=
  required_minimal Capability.certifiedVerifierExpansion

theorem callableUpgrade_minimal :
    graph.InclusionMinimal
      (required Capability.boundedCallableUpgrade)
      {Capability.boundedCallableUpgrade} :=
  required_minimal Capability.boundedCallableUpgrade

theorem jointLongRunStability_minimal :
    graph.InclusionMinimal
      (required Capability.jointLongRunStability)
      {Capability.jointLongRunStability} :=
  required_minimal Capability.jointLongRunStability

theorem proofCheckedExpansion_minimal :
    graph.InclusionMinimal
      (required Capability.proofCheckedVerifierExpansion)
      {Capability.proofCheckedVerifierExpansion} :=
  required_minimal Capability.proofCheckedVerifierExpansion

theorem finiteStrictGrowthBound_minimal :
    graph.InclusionMinimal
      (required Capability.finiteStrictGrowthBound)
      {Capability.finiteStrictGrowthBound} :=
  required_minimal Capability.finiteStrictGrowthBound

theorem proofBoundedCallableExpansion_minimal :
    graph.InclusionMinimal
      (required Capability.proofBoundedCallableExpansion)
      {Capability.proofBoundedCallableExpansion} :=
  required_minimal Capability.proofBoundedCallableExpansion

end AdvancedRSIDependencyGraph
end DistinctionSelfReference
