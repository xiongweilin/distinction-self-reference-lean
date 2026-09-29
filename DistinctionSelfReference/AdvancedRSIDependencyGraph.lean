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
  deriving DecidableEq, Repr

inductive Capability
  | certifiedVerifierExpansion
  | strictCapabilityGrowth
  | boundedCallableUpgrade
  | realityConvergence
  | jointLongRunStability
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

end AdvancedRSIDependencyGraph
end DistinctionSelfReference
