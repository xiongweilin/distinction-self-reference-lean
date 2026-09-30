import DistinctionSelfReference.TaskRelativeScheduling

namespace DistinctionSelfReference
namespace TaskFamilyScheduling

open LongRunRSI
open VariableDelayReality
open SchedulingCriterion
open TaskRelativeScheduling

/--
A stable Boolean task packages the signal, its eventual target, and the fact
that the signal actually stabilizes to that target.
-/
structure StableTask where
  signal : Nat → Bool
  target : Bool
  stable : EventuallyConstant signal target

/-- The schedule preserves the eventual target of one already-stable task. -/
def PreservesStableTask (S : Schedule) (t : StableTask) : Prop :=
  EventuallyConstant (fun n => t.signal (S.source n)) t.target

/--
A schedule eventually avoids every source index at which the task disagrees
with its eventual target.
-/
def EventuallyAvoidsTaskErrors (S : Schedule) (t : StableTask) : Prop :=
  ∃ N, ∀ n ≥ N, t.signal (S.source n) = t.target

theorem preservesStableTask_iff_eventuallyAvoidsErrors
    (S : Schedule) (t : StableTask) :
    PreservesStableTask S t ↔ EventuallyAvoidsTaskErrors S t := by
  rfl

/-- Preservation of every task in a chosen family. -/
def PreservesFamily (S : Schedule) (family : Set StableTask) : Prop :=
  ∀ t, t ∈ family → PreservesStableTask S t

/--
The exact task-family scheduling criterion: eventually avoid the error set of
every task in the family.
-/
def FamilySchedulingCriterion
    (S : Schedule) (family : Set StableTask) : Prop :=
  ∀ t, t ∈ family → EventuallyAvoidsTaskErrors S t

theorem preservesFamily_iff_criterion
    (S : Schedule) (family : Set StableTask) :
    PreservesFamily S family ↔ FamilySchedulingCriterion S family := by
  rfl

/-- Universal eventual freshness is sufficient for every stable task family. -/
theorem eventuallyFresh_implies_familyCriterion
    (S : Schedule)
    (hfresh : S.EventuallyFresh)
    (family : Set StableTask) :
    FamilySchedulingCriterion S family := by
  intro t _
  exact preservesStableBool_of_eventuallyFresh S hfresh
    t.signal t.target t.stable

namespace StrictnessExample

def oneTransientStableTask : StableTask where
  signal := TaskRelativeScheduling.StrictnessExample.oneTransientTask
  target := false
  stable := TaskRelativeScheduling.StrictnessExample.oneTransientTask_stable

def singletonFamily : Set StableTask :=
  {oneTransientStableTask}

theorem staleAtOne_satisfies_singleton_criterion :
    FamilySchedulingCriterion
      TaskRelativeScheduling.StrictnessExample.staleAtOne
      singletonFamily := by
  intro t ht
  simp only [singletonFamily, Set.mem_singleton_iff] at ht
  subst t
  exact TaskRelativeScheduling.StrictnessExample.staleAtOne_preserves_oneTransientTask

/--
For a fixed nontrivial task family, the sharp family criterion can be strictly
weaker than global eventual freshness.
-/
theorem familyCriterion_strictly_weaker_than_eventualFreshness :
    (¬ TaskRelativeScheduling.StrictnessExample.staleAtOne.EventuallyFresh) ∧
    FamilySchedulingCriterion
      TaskRelativeScheduling.StrictnessExample.staleAtOne
      singletonFamily :=
  ⟨TaskRelativeScheduling.StrictnessExample.staleAtOne_not_eventuallyFresh,
    staleAtOne_satisfies_singleton_criterion⟩

end StrictnessExample

end TaskFamilyScheduling
end DistinctionSelfReference
