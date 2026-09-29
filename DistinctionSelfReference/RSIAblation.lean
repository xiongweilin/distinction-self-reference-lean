import DistinctionSelfReference.GuardedRSI
import DistinctionSelfReference.CorrigibilityAblation

namespace DistinctionSelfReference
namespace RSIAblation

open SelfModification
open CapabilityOrder
open VerifierMigration

/-- Safety invariant used by the minimal verifier countermodel. -/
def falseInvariant (b : Bool) : Prop :=
  b = false

def acceptsAll : Verifier Bool where
  accepts := fun _ => True

def falseToTrue : Proposal Bool where
  before := false
  after := true

/-- Acceptance without verifier soundness can immediately violate an invariant. -/
theorem acceptsAll_not_sound :
    ¬ acceptsAll.SoundFor falseInvariant := by
  intro h
  have hbad := h falseToTrue trivial
  change true = false at hbad
  exact Bool.false_ne_true hbad.symm

/-- A capability-aware version with every Bool capability. -/
def fullCapabilities : CapVersion Bool Unit where
  payload := Unit.unit
  profile := ⟨Set.univ⟩

/-- A degraded version retaining only the false-labelled capability. -/
def falseOnlyCapabilities : CapVersion Bool Unit where
  payload := Unit.unit
  profile := ⟨{false}⟩

def degradingProposal : Proposal (CapVersion Bool Unit) where
  before := fullCapabilities
  after := falseOnlyCapabilities

/-- Self-modification does not imply capability monotonicity without a non-degradation condition. -/
theorem degradingProposal_not_nonDegrading :
    ¬ CapVersion.NonDegrading degradingProposal := by
  intro h
  have htrue := h (Set.mem_univ true)
  change true = false at htrue
  exact Bool.false_ne_true htrue.symm

/-- Old verifier accepts only proposals whose target satisfies the invariant. -/
def safeVerifier : Verifier Bool where
  accepts := fun p => p.after = false

/-- A migrated verifier that accepts everything. -/
def permissiveVerifier : Verifier Bool where
  accepts := fun _ => True

theorem safeVerifier_sound :
    safeVerifier.SoundFor falseInvariant := by
  intro p hp
  exact hp

/-- Unconstrained verifier self-modification can lose soundness. -/
theorem permissiveVerifier_not_sound :
    ¬ permissiveVerifier.SoundFor falseInvariant := by
  intro h
  have hbad := h falseToTrue trivial
  change true = false at hbad
  exact Bool.false_ne_true hbad.symm

/-- The unsafe migration is excluded by the refinement condition. -/
theorem permissive_not_refine_safe :
    ¬ Refines permissiveVerifier safeVerifier := by
  intro h
  have hp := h falseToTrue trivial
  change true = false at hp
  exact Bool.false_ne_true hp.symm

/--
Reality correction is likewise independent: the earlier missed-detection model
already has a correct revision proposal but fails to correct the actual mismatch.
-/
theorem revision_without_detection_not_reality_grounded :
    ¬ (∀ world,
      CorrigibilityAblation.missedDetection.retained ≠
        CorrigibilityAblation.missedDetection.required world →
      CorrigibilityAblation.missedDetection.applied world =
        CorrigibilityAblation.missedDetection.required world) :=
  CorrigibilityAblation.missedDetection_not_correctMismatch

end RSIAblation
end DistinctionSelfReference
