import DistinctionSelfReference.Reopening
import DistinctionSelfReference.Recovery
import DistinctionSelfReference.Bisimulation

namespace DistinctionSelfReference
namespace Corrigibility

open Reopening
open Recovery
open Viability

universe u v w x y z

/-- Operational context for asking whether a corrected commitment is recoverable. -/
structure RecoveryContext
    (World : Type u) (Obs : Type v) (Boundary : Type w)
    (State : Type x) (Action : Type y) where
  revision : Reopening.System World Obs Boundary
  control : ControlledSystem State Action
  stateAfter : Boundary → State

namespace RecoveryContext

variable
  {World : Type u} {Obs : Type v} {Boundary : Type w}
  {State : Type x} {Action : Type y}

/-- Every reality-required boundary maps to a recoverable control state. -/
def RequiredRecoverable
    (K : RecoveryContext World Obs Boundary State Action) : Prop :=
  ∀ world, Recoverable K.control (K.stateAfter (K.revision.required world))

/--
On an actual mismatch, detection + successful revision + recoverability of the
required boundary produce finite recovery after correction.
-/
theorem recoverable_after_mismatch
    (K : RecoveryContext World Obs Boundary State Action)
    (hdetect : K.revision.DetectsMismatch)
    (hsuccess : K.revision.RevisionSucceeds)
    (hrecover : K.RequiredRecoverable)
    {world : World}
    (hmismatch : K.revision.retained ≠ K.revision.required world) :
    Recoverable K.control (K.stateAfter (K.revision.applied world)) := by
  rw [K.revision.corrects_mismatch hdetect hsuccess hmismatch]
  exact hrecover world

/--
Adding false-alarm rejection upgrades mismatch-only recovery to recovery after
the applied policy in every world.
-/
theorem recoverable_after_exact_correction
    (K : RecoveryContext World Obs Boundary State Action)
    (hdetect : K.revision.DetectsMismatch)
    (hsuccess : K.revision.RevisionSucceeds)
    (hstable : K.revision.RejectsFalseAlarm)
    (hrecover : K.RequiredRecoverable) :
    ∀ world, Recoverable K.control (K.stateAfter (K.revision.applied world)) := by
  intro world
  rw [K.revision.exact_correction hdetect hsuccess hstable world]
  exact hrecover world

end RecoveryContext

/--
A chosen behavioral identity criterion on boundaries. Revision is continuous
when the retained and proposed revised boundaries remain bisimilar.
-/
structure ContinuityContext
    (World : Type u) (Obs : Type v) (Boundary : Type w)
    (IdentityObs : Type z) where
  revision : Reopening.System World Obs Boundary
  identity : Bisimulation.System Boundary IdentityObs

namespace ContinuityContext

variable
  {World : Type u} {Obs : Type v} {Boundary : Type w}
  {IdentityObs : Type z}

/-- Every mismatch-triggered revision preserves the selected behavioral identity. -/
def PreservesContinuity
    (K : ContinuityContext World Obs Boundary IdentityObs) : Prop :=
  ∀ world, K.revision.retained ≠ K.revision.required world →
    K.identity.Bisimilar K.revision.retained
      (K.revision.revise (K.revision.observe world))

/--
Corrigibility and self-continuity are compatible when successful revision is
bisimilar to the retained boundary under the chosen identity criterion.
-/
theorem continuous_correction_on_mismatch
    (K : ContinuityContext World Obs Boundary IdentityObs)
    (hdetect : K.revision.DetectsMismatch)
    (hsuccess : K.revision.RevisionSucceeds)
    (hcontinuity : K.PreservesContinuity)
    {world : World}
    (hmismatch : K.revision.retained ≠ K.revision.required world) :
    K.revision.applied world = K.revision.required world ∧
      K.identity.Bisimilar K.revision.retained (K.revision.applied world) := by
  have hcorrect :=
    K.revision.corrects_mismatch hdetect hsuccess hmismatch
  have happlied :
      K.revision.applied world =
        K.revision.revise (K.revision.observe world) := by
    unfold Reopening.System.applied Reopening.System.applyObservation
    rw [hdetect world hmismatch]
    simp
  constructor
  · exact hcorrect
  · rw [happlied]
    exact hcontinuity world hmismatch

end ContinuityContext
end Corrigibility
end DistinctionSelfReference
