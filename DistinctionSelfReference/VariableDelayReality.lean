import DistinctionSelfReference.JointRSIConvergence

namespace DistinctionSelfReference
namespace VariableDelayReality

open LongRunRSI

universe u

/-- The observation used at update n may come from an arbitrary source index. -/
structure Schedule where
  source : Nat → Nat

namespace Schedule

/-- No update reads from the future. -/
def Causal (S : Schedule) : Prop :=
  ∀ n, S.source n ≤ n

/--
Every finite stale prefix is eventually left behind. This permits variable
delay and out-of-order observations; monotonicity of source is not required.
-/
def EventuallyFresh (S : Schedule) : Prop :=
  ∀ cutoff, ∃ N, ∀ n, N ≤ n → cutoff ≤ S.source n

/-- A fixed upper bound on staleness. -/
def BoundedStaleness (S : Schedule) (lag : Nat) : Prop :=
  ∀ n, n ≤ S.source n + lag

theorem eventuallyFresh_of_boundedStaleness
    (S : Schedule)
    (lag : Nat)
    (hbound : S.BoundedStaleness lag) :
    S.EventuallyFresh := by
  intro cutoff
  refine ⟨cutoff + lag, ?_⟩
  intro n hn
  have h := hbound n
  omega

end Schedule

/-- Retained state at update n equals the requirement read from its source index. -/
def TracksSchedule
    (S : Schedule)
    {Boundary : Type u}
    (required retained : Nat → Boundary) : Prop :=
  ∀ n, retained n = required (S.source n)

/--
Eventual freshness is exactly the scheduling property needed to transport
eventual requirement stability through arbitrary variable delay/reordering.
-/
theorem retained_converges_of_eventuallyFresh
    {Boundary : Type u}
    (S : Schedule)
    {required retained : Nat → Boundary}
    {target : Boundary}
    (hfresh : S.EventuallyFresh)
    (htrack : TracksSchedule S required retained)
    (hreq : EventuallyConstant required target) :
    EventuallyConstant retained target := by
  rcases hreq with ⟨cutoff, hcutoff⟩
  rcases hfresh cutoff with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  rw [htrack n]
  exact hcutoff (S.source n) (hN n hn)

/-- Bounded staleness is a concrete sufficient scheduling condition. -/
theorem retained_converges_of_boundedStaleness
    {Boundary : Type u}
    (S : Schedule)
    (lag : Nat)
    {required retained : Nat → Boundary}
    {target : Boundary}
    (hbound : S.BoundedStaleness lag)
    (htrack : TracksSchedule S required retained)
    (hreq : EventuallyConstant required target) :
    EventuallyConstant retained target :=
  retained_converges_of_eventuallyFresh S
    (S.eventuallyFresh_of_boundedStaleness lag hbound) htrack hreq

namespace ReorderedExample

/-- One deliberately reordered schedule: update 3 reuses source 1. -/
def schedule : Schedule where
  source n := if n = 3 then 1 else n

theorem causal : schedule.Causal := by
  intro n
  by_cases h : n = 3
  · subst n
    simp [schedule]
  · simp [schedule, h]

theorem bounded : schedule.BoundedStaleness 2 := by
  intro n
  by_cases h : n = 3
  · subst n
    simp [schedule]
  · simp [schedule, h]

theorem not_monotone_source :
    ¬ Monotone schedule.source := by
  intro h
  have h23 := h (show 2 ≤ 3 by decide)
  simp [schedule] at h23

end ReorderedExample

namespace StaleCounterexample

def source : Schedule where
  source := fun _ => 0

def required : Nat → Bool
  | 0 => false
  | _ + 1 => true

def retained (_ : Nat) : Bool := false

theorem tracks :
    TracksSchedule source required retained := by
  intro n
  rfl

theorem requirement_converges :
    EventuallyConstant required true := by
  refine ⟨1, ?_⟩
  intro n hn
  cases n with
  | zero => omega
  | succ n => rfl

/-- Permanently stale observations can destroy eventual reality alignment. -/
theorem retained_not_convergent :
    ¬ EventuallyConstant retained true := by
  rintro ⟨N, hN⟩
  have h := hN N le_rfl
  simp [retained] at h

end StaleCounterexample
end VariableDelayReality
end DistinctionSelfReference
