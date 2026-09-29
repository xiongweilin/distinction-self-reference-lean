import DistinctionSelfReference.LocalSufficiency

namespace DistinctionSelfReference
namespace Reopening

open LocalSufficiency

universe u v w

/--
A retained boundary plus a reality-dependent requirement and an observation-
driven gate/revision policy.
-/
structure System (World : Type u) (Obs : Type v) (Boundary : Type w) where
  observe : World → Obs
  required : World → Boundary
  retained : Boundary
  reopen : Obs → Bool
  revise : Obs → Boundary

namespace System

variable {World : Type u} {Obs : Type v} {Boundary : Type w}

/-- Boundary selected after consulting the current observation. -/
def applyObservation (S : System World Obs Boundary) (o : Obs) : Boundary :=
  if S.reopen o then S.revise o else S.retained

/-- Applied boundary in one reality state. -/
def applied (S : System World Obs Boundary) (world : World) : Boundary :=
  S.applyObservation (S.observe world)

/-- Every actual retained/required mismatch opens the boundary. -/
def DetectsMismatch (S : System World Obs Boundary) : Prop :=
  ∀ world, S.retained ≠ S.required world →
    S.reopen (S.observe world) = true

/-- Already-correct boundaries are not spuriously reopened. -/
def RejectsFalseAlarm (S : System World Obs Boundary) : Prop :=
  ∀ world, S.retained = S.required world →
    S.reopen (S.observe world) = false

/-- When a mismatch exists, the proposed revision is reality-correct. -/
def RevisionSucceeds (S : System World Obs Boundary) : Prop :=
  ∀ world, S.retained ≠ S.required world →
    S.revise (S.observe world) = S.required world

theorem corrects_mismatch
    (S : System World Obs Boundary)
    (hdetect : S.DetectsMismatch)
    (hsuccess : S.RevisionSucceeds)
    {world : World}
    (hmismatch : S.retained ≠ S.required world) :
    S.applied world = S.required world := by
  unfold applied applyObservation
  rw [hdetect world hmismatch]
  exact hsuccess world hmismatch

theorem preserves_match
    (S : System World Obs Boundary)
    (hstable : S.RejectsFalseAlarm)
    {world : World}
    (hmatch : S.retained = S.required world) :
    S.applied world = S.required world := by
  unfold applied applyObservation
  rw [hstable world hmatch]
  exact hmatch

/--
Detection + successful revision + no false reopening give exact correction in
every world.
-/
theorem exact_correction
    (S : System World Obs Boundary)
    (hdetect : S.DetectsMismatch)
    (hsuccess : S.RevisionSucceeds)
    (hstable : S.RejectsFalseAlarm) :
    ∀ world, S.applied world = S.required world := by
  intro world
  by_cases h : S.retained = S.required world
  · exact S.preserves_match hstable h
  · exact S.corrects_mismatch hdetect hsuccess h

/--
Exact corrigibility implies that the current observation is sufficient for the
required commitment: the applied revision policy is the post-processing map.
-/
theorem localSufficiency_of_exactCorrection
    (S : System World Obs Boundary)
    (hdetect : S.DetectsMismatch)
    (hsuccess : S.RevisionSucceeds)
    (hstable : S.RejectsFalseAlarm) :
    Sufficient S.observe S.required := by
  refine ⟨S.applyObservation, ?_⟩
  funext world
  exact (S.exact_correction hdetect hsuccess hstable world).symm

end System
end Reopening
end DistinctionSelfReference
