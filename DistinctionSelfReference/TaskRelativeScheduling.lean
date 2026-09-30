import DistinctionSelfReference.SchedulingCriterion

namespace DistinctionSelfReference
namespace TaskRelativeScheduling

open LongRunRSI
open VariableDelayReality
open SchedulingCriterion

/--
A schedule is adequate for one fixed eventually-stable task when scheduled
sampling preserves that task's eventual target.
-/
def PreservesTask
    (S : Schedule)
    (required : Nat → Bool)
    (target : Bool) : Prop :=
  EventuallyConstant required target →
  EventuallyConstant (fun n => required (S.source n)) target

theorem eventuallyFresh_preserves_task
    (S : Schedule)
    (hfresh : S.EventuallyFresh)
    (required : Nat → Bool)
    (target : Bool) :
    PreservesTask S required target := by
  intro hstable
  exact preservesStableBool_of_eventuallyFresh S hfresh
    required target hstable

/--
Universal preservation is exactly preservation of every individual task.
-/
theorem preservesStableBool_iff_all_tasks
    (S : Schedule) :
    PreservesStableBool S ↔
      ∀ required target, PreservesTask S required target := by
  constructor
  · intro hall required target hstable
    exact hall required target hstable
  · intro hall required target hstable
    exact hall required target hstable

namespace StrictnessExample

/-- Permanently read source index 1. This is not eventually fresh. -/
def staleAtOne : Schedule where
  source := fun _ => 1

theorem staleAtOne_not_eventuallyFresh :
    ¬ staleAtOne.EventuallyFresh := by
  intro hfresh
  rcases hfresh 2 with ⟨N, hN⟩
  have h := hN N (Nat.le_refl N)
  simp [staleAtOne] at h

/--
A nonconstant task that stabilizes to false after time 0. Although the schedule
is globally stale, it samples index 1, which is already on the final task value.
-/
def oneTransientTask : Nat → Bool
  | 0 => true
  | _ + 1 => false

theorem oneTransientTask_stable :
    EventuallyConstant oneTransientTask false := by
  refine ⟨1, ?_⟩
  intro n hn
  cases n with
  | zero =>
      omega
  | succ n =>
      rfl

theorem staleAtOne_preserves_oneTransientTask :
    PreservesTask staleAtOne oneTransientTask false := by
  intro _
  refine ⟨0, ?_⟩
  intro n _
  simp [staleAtOne, oneTransientTask]

/--
Task-relative adequacy is strictly weaker than universal eventual freshness:
a schedule can fail freshness globally yet remain perfectly adequate for a
specific nonconstant eventually-stable task.
-/
theorem task_relative_preservation_strictly_weaker :
    (¬ staleAtOne.EventuallyFresh) ∧
    PreservesTask staleAtOne oneTransientTask false :=
  ⟨staleAtOne_not_eventuallyFresh,
    staleAtOne_preserves_oneTransientTask⟩

end StrictnessExample

end TaskRelativeScheduling
end DistinctionSelfReference
