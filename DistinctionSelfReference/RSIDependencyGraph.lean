import DistinctionSelfReference.MetaFramework

namespace DistinctionSelfReference
namespace RSIDependencyGraph

open MetaFramework

/-- Independently isolatable assumptions in the first RSI construction layer. -/
inductive Condition
  | capabilityOrder
  | selfModification
  | verifierSoundness
  | nonDegradation
  | invariantSpecification
  | realityFeedback
  | mismatchDetection
  | revisionSuccess
  | falseAlarmRejection
  | verifierRefinement
  deriving DecidableEq, Repr

inductive Capability
  | capabilityMonotoneUpgrade
  | invariantPreservingUpgrade
  | realityTrackedRevision
  | trustedVerifierMigration
  | guardedRSILoop
  deriving DecidableEq, Repr

def required : Capability → Set Condition
  | .capabilityMonotoneUpgrade =>
      { .capabilityOrder, .selfModification, .nonDegradation }
  | .invariantPreservingUpgrade =>
      { .selfModification, .verifierSoundness, .invariantSpecification }
  | .realityTrackedRevision =>
      { .realityFeedback, .mismatchDetection,
        .revisionSuccess, .falseAlarmRejection }
  | .trustedVerifierMigration =>
      { .verifierSoundness, .verifierRefinement }
  | .guardedRSILoop =>
      { .capabilityOrder, .selfModification, .verifierSoundness,
        .nonDegradation, .invariantSpecification, .realityFeedback,
        .mismatchDetection, .revisionSuccess, .falseAlarmRejection,
        .verifierRefinement }

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

theorem guardedRSI_minimal :
    graph.InclusionMinimal
      (required Capability.guardedRSILoop)
      {Capability.guardedRSILoop} :=
  required_minimal Capability.guardedRSILoop

end RSIDependencyGraph
end DistinctionSelfReference
