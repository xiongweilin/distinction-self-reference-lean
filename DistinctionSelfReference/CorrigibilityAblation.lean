import DistinctionSelfReference.CorrigibilityDependencyGraph
import DistinctionSelfReference.FeasibleFramework
import DistinctionSelfReference.Reopening

namespace DistinctionSelfReference
namespace CorrigibilityAblation

open Reopening
open MetaFramework
open CorrigibilityDependencyGraph

/-- Fully working Boolean reopening model. -/
def good : Reopening.System Bool Bool Bool where
  observe := id
  required := id
  retained := false
  reopen := id
  revise := id

theorem good_detectsMismatch : good.DetectsMismatch := by
  intro world h
  cases world with
  | false => exact (h rfl).elim
  | true => rfl

theorem good_revisionSucceeds : good.RevisionSucceeds := by
  intro world h
  cases world with
  | false => exact (h rfl).elim
  | true => rfl

theorem good_rejectsFalseAlarm : good.RejectsFalseAlarm := by
  intro world h
  cases world with
  | false => rfl
  | true => exact (Bool.false_ne_true h).elim

theorem good_exactCorrection :
    ∀ world, good.applied world = good.required world :=
  good.exact_correction
    good_detectsMismatch good_revisionSucceeds good_rejectsFalseAlarm

/-- Revision can be correct while the mismatch gate never opens. -/
def missedDetection : Reopening.System Bool Bool Bool where
  observe := id
  required := id
  retained := false
  reopen := fun _ => false
  revise := id

theorem missedDetection_revisionSucceeds :
    missedDetection.RevisionSucceeds := by
  intro world h
  cases world with
  | false => exact (h rfl).elim
  | true => rfl

theorem missedDetection_not_detectsMismatch :
    ¬ missedDetection.DetectsMismatch := by
  intro h
  have hx := h true Bool.false_ne_true
  change false = true at hx
  exact Bool.false_ne_true hx

theorem missedDetection_not_correctMismatch :
    ¬ (∀ world, missedDetection.retained ≠ missedDetection.required world →
        missedDetection.applied world = missedDetection.required world) := by
  intro h
  have hx := h true Bool.false_ne_true
  change false = true at hx
  exact Bool.false_ne_true hx

/-- The gate can open correctly while the proposed revision remains wrong. -/
def failedRevision : Reopening.System Bool Bool Bool where
  observe := id
  required := id
  retained := false
  reopen := id
  revise := fun _ => false

theorem failedRevision_detectsMismatch :
    failedRevision.DetectsMismatch := by
  intro world h
  cases world with
  | false => exact (h rfl).elim
  | true => rfl

theorem failedRevision_not_revisionSucceeds :
    ¬ failedRevision.RevisionSucceeds := by
  intro h
  have hx := h true Bool.false_ne_true
  change false = true at hx
  exact Bool.false_ne_true hx

theorem failedRevision_not_correctMismatch :
    ¬ (∀ world, failedRevision.retained ≠ failedRevision.required world →
        failedRevision.applied world = failedRevision.required world) := by
  intro h
  have hx := h true Bool.false_ne_true
  change false = true at hx
  exact Bool.false_ne_true hx

/--
Detection and mismatch-success can both hold while false alarms corrupt a
boundary that was already correct.
-/
def spuriousReopening : Reopening.System Bool Bool Bool where
  observe := id
  required := id
  retained := false
  reopen := fun _ => true
  revise := fun _ => true

theorem spuriousReopening_detectsMismatch :
    spuriousReopening.DetectsMismatch := by
  intro _ _
  rfl

theorem spuriousReopening_revisionSucceeds :
    spuriousReopening.RevisionSucceeds := by
  intro world h
  cases world with
  | false => exact (h rfl).elim
  | true => rfl

theorem spuriousReopening_not_rejectsFalseAlarm :
    ¬ spuriousReopening.RejectsFalseAlarm := by
  intro h
  have hx := h false rfl
  change true = false at hx
  exact Bool.true_ne_false hx

theorem spuriousReopening_not_exactCorrection :
    ¬ (∀ world, spuriousReopening.applied world =
        spuriousReopening.required world) := by
  intro h
  have hx := h false
  change true = false at hx
  exact Bool.true_ne_false hx

/--
Semantic interpretation of the core three reopening conditions. The recovery
and continuity conditions belong to richer contexts and are left unconstrained
in this small realization layer.
-/
def coreSemantics : ConditionSemantics Condition where
  Realization := Reopening.System Bool Bool Bool
  holds S c :=
    match c with
    | .mismatchDetection => S.DetectsMismatch
    | .revisionSuccess => S.RevisionSucceeds
    | .falseAlarmRejection => S.RejectsFalseAlarm
    | .requiredRecoverability => True
    | .continuityPreservation => True

theorem exactConditions_compatible :
    coreSemantics.Compatible
      {Condition.mismatchDetection, Condition.revisionSuccess,
        Condition.falseAlarmRejection} := by
  refine ⟨good, ?_⟩
  intro c hc
  cases c with
  | mismatchDetection => exact good_detectsMismatch
  | revisionSuccess => exact good_revisionSucceeds
  | falseAlarmRejection => exact good_rejectsFalseAlarm
  | requiredRecoverability => trivial
  | continuityPreservation => trivial

/--
The exact-correction condition triple is not only graph-minimal but jointly
realizable, hence a concrete feasible inclusion-minimal framework.
-/
theorem exactCorrection_feasible_minimal :
    FeasibleInclusionMinimal graph coreSemantics
      {Condition.mismatchDetection, Condition.revisionSuccess,
        Condition.falseAlarmRejection}
      {Capability.exactCorrection} := by
  apply feasibleInclusionMinimal_of_inclusionMinimal_of_compatible
  · exact exactCorrection_minimal
  · exact exactConditions_compatible

end CorrigibilityAblation
end DistinctionSelfReference
