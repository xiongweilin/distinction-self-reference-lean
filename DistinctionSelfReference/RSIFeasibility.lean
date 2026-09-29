import DistinctionSelfReference.GuardedRSI
import DistinctionSelfReference.FeasibleFramework
import DistinctionSelfReference.RSIDependencyGraph

namespace DistinctionSelfReference
namespace RSIFeasibility

open SelfModification
open MetaFramework
open RSIDependencyGraph

/-- Trivial modifier used only to witness joint realizability of the guarded conditions. -/
def modifier : Modifier (CapVersion Bool Unit) where
  propose := id

def version : CapVersion Bool Unit where
  payload := Unit.unit
  profile := ⟨{false}⟩

def verifier : Verifier (CapVersion Bool Unit) where
  accepts p := p.after = p.before

def invariant (_ : CapVersion Bool Unit) : Prop :=
  True

def realitySystem : IteratedReopening.System Bool Bool Bool where
  observe := id
  required := id
  reopen current obs := current != obs
  revise _ obs := obs

theorem reality_detects :
    realitySystem.DetectsMismatch := by
  intro current world h
  cases current <;> cases world <;> simp_all [realitySystem]

theorem reality_revisionSucceeds :
    realitySystem.RevisionSucceeds := by
  intro current world h
  cases current <;> cases world <;> simp_all [realitySystem]

theorem reality_rejectsFalseAlarm :
    realitySystem.RejectsFalseAlarm := by
  intro current world h
  cases current <;> cases world <;> simp_all [realitySystem]

def loop : GuardedRSI.Loop Bool Unit Bool Bool Bool where
  modifier := modifier
  versions := fun _ => version
  verifiers := fun _ => verifier
  invariant := invariant
  initialVerifierSound := by
    intro _ _
    trivial
  verifierMigration := by
    intro _ p hp
    exact hp
  verifiedStep := by
    intro _
    constructor
    · rfl
    · rfl
  acceptedNonDegrading := by
    intro _ p hp
    change p.before.profile ≤ p.after.profile
    have heq : p.after = p.before := hp
    rw [heq]
  realitySystem := realitySystem
  reality := fun _ => false
  initialBoundary := false
  detectsMismatch := reality_detects
  revisionSucceeds := reality_revisionSucceeds
  rejectsFalseAlarm := reality_rejectsFalseAlarm

/--
Interpret the first RSI condition language directly against one guarded loop.
Structural fields are genuine properties of the realization, not merely graph
annotations.
-/
def semantics : ConditionSemantics Condition where
  Realization := GuardedRSI.Loop Bool Unit Bool Bool Bool
  holds L c :=
    match c with
    | .capabilityOrder => True
    | .selfModification => True
    | .verifierSoundness => (L.verifiers 0).SoundFor L.invariant
    | .nonDegradation => ∀ n p, (L.verifiers n).accepts p → CapVersion.NonDegrading p
    | .invariantSpecification => True
    | .realityFeedback => True
    | .mismatchDetection => L.realitySystem.DetectsMismatch
    | .revisionSuccess => L.realitySystem.RevisionSucceeds
    | .falseAlarmRejection => L.realitySystem.RejectsFalseAlarm
    | .verifierRefinement => VerifierMigration.MigrationChain L.verifiers

theorem guardedConditions_compatible :
    semantics.Compatible (required Capability.guardedRSILoop) := by
  refine ⟨loop, ?_⟩
  intro c hc
  cases c <;> simp [semantics, required] at hc ⊢
  · exact loop.initialVerifierSound
  · exact loop.acceptedNonDegrading
  · exact loop.detectsMismatch
  · exact loop.revisionSucceeds
  · exact loop.rejectsFalseAlarm
  · exact loop.verifierMigration

/--
The original guarded-RSI condition set is now both inclusion-minimal in the
capability graph and jointly realizable.
-/
theorem guardedRSI_feasible_minimal :
    FeasibleInclusionMinimal graph semantics
      (required Capability.guardedRSILoop)
      {Capability.guardedRSILoop} := by
  apply feasibleInclusionMinimal_of_inclusionMinimal_of_compatible
  · exact guardedRSI_minimal
  · exact guardedConditions_compatible

end RSIFeasibility
end DistinctionSelfReference
