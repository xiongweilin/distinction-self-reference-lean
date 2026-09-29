import DistinctionSelfReference.VerifiedUpgrade
import DistinctionSelfReference.VerifierMigration
import DistinctionSelfReference.IteratedReopening

namespace DistinctionSelfReference
namespace GuardedRSI

open CapabilityOrder
open SelfModification
open VerifierMigration

universe u v w x y

/--
A first guarded RSI scaffold: versions may self-modify, verifiers may migrate
conservatively, and an independent reality-facing loop repeatedly reopens a
retained boundary.
-/
structure Loop
    (Capability : Type u) (Payload : Type v)
    (World : Type w) (Obs : Type x) (Boundary : Type y) where
  modifier : Modifier (CapVersion Capability Payload)
  versions : ℕ → CapVersion Capability Payload
  verifiers : ℕ → Verifier (CapVersion Capability Payload)
  invariant : CapVersion Capability Payload → Prop
  initialVerifierSound :
    (verifiers 0).SoundFor invariant
  verifierMigration :
    VerifierMigration.MigrationChain verifiers
  verifiedStep :
    ∀ n, modifier.VerifiedStep (verifiers n) (versions n) (versions (n + 1))
  acceptedNonDegrading :
    ∀ n p, (verifiers n).accepts p → CapVersion.NonDegrading p

  realitySystem : IteratedReopening.System World Obs Boundary
  reality : ℕ → World
  initialBoundary : Boundary
  detectsMismatch : realitySystem.DetectsMismatch
  revisionSucceeds : realitySystem.RevisionSucceeds
  rejectsFalseAlarm : realitySystem.RejectsFalseAlarm

namespace Loop

variable
  {Capability : Type u} {Payload : Type v}
  {World : Type w} {Obs : Type x} {Boundary : Type y}

/-- Every migrated verifier remains sound for the original invariant. -/
theorem verifier_sound
    (L : Loop Capability Payload World Obs Boundary) :
    ∀ n, (L.verifiers n).SoundFor L.invariant := by
  exact VerifierMigration.soundness_along_chain
    L.verifierMigration L.invariant L.initialVerifierSound

/-- Every completed self-modification step satisfies the invariant. -/
theorem invariant_after_step
    (L : Loop Capability Payload World Obs Boundary) :
    ∀ n, L.invariant (L.versions (n + 1)) := by
  intro n
  exact L.modifier.verifiedStep_preserves_invariant
    (L.verifiers n) L.invariant (L.verifier_sound n) (L.verifiedStep n)

/-- Every self-modification step is non-degrading in the capability order. -/
theorem capability_step_mono
    (L : Loop Capability Payload World Obs Boundary) :
    ∀ n, (L.versions n).profile ≤ (L.versions (n + 1)).profile := by
  intro n
  have hstep := L.verifiedStep n
  rcases hstep with ⟨hnext, haccept⟩
  have hnon := L.acceptedNonDegrading n (L.modifier.proposal (L.versions n)) haccept
  rw [hnext]
  exact hnon

/-- Hence the complete version chain is monotone in capability. -/
theorem capability_chain_mono
    (L : Loop Capability Payload World Obs Boundary) :
    Monotone (fun n => (L.versions n).profile) := by
  apply CapabilityOrder.chain_mono
  exact L.capability_step_mono

/-- The reality-facing boundary tracks every observed reality requirement. -/
theorem reality_tracks
    (L : Loop Capability Payload World Obs Boundary) :
    ∀ n,
      L.realitySystem.trajectory L.initialBoundary L.reality (n + 1) =
        L.realitySystem.required (L.reality n) := by
  intro n
  exact L.realitySystem.trajectory_tracks_reality
    L.detectsMismatch L.revisionSucceeds L.rejectsFalseAlarm
    L.initialBoundary L.reality n

/--
The guarded loop therefore exposes four guarantees without identifying them:
trusted verifier migration, invariant preservation, capability monotonicity,
and reality-grounded correction.
-/
theorem guarantees
    (L : Loop Capability Payload World Obs Boundary)
    (n : ℕ) :
    (L.verifiers n).SoundFor L.invariant ∧
      L.invariant (L.versions (n + 1)) ∧
      (L.versions n).profile ≤ (L.versions (n + 1)).profile ∧
      L.realitySystem.trajectory L.initialBoundary L.reality (n + 1) =
        L.realitySystem.required (L.reality n) := by
  exact ⟨L.verifier_sound n, L.invariant_after_step n,
    L.capability_step_mono n, L.reality_tracks n⟩

end Loop
end GuardedRSI
end DistinctionSelfReference
