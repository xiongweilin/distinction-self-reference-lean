import DistinctionSelfReference.LocalSufficiency

namespace DistinctionSelfReference
namespace IteratedReopening

open LocalSufficiency

universe u v w

/--
Repeated reality-facing revision. Unlike the one-shot reopening model, the gate
and revision rule may depend on the currently retained boundary.
-/
structure System (World : Type u) (Obs : Type v) (Boundary : Type w) where
  observe : World → Obs
  required : World → Boundary
  reopen : Boundary → Obs → Bool
  revise : Boundary → Obs → Boundary

namespace System

variable {World : Type u} {Obs : Type v} {Boundary : Type w}

def update
    (S : System World Obs Boundary)
    (current : Boundary) (world : World) : Boundary :=
  if S.reopen current (S.observe world) then
    S.revise current (S.observe world)
  else current

def DetectsMismatch (S : System World Obs Boundary) : Prop :=
  ∀ current world, current ≠ S.required world →
    S.reopen current (S.observe world) = true

def RejectsFalseAlarm (S : System World Obs Boundary) : Prop :=
  ∀ current world, current = S.required world →
    S.reopen current (S.observe world) = false

def RevisionSucceeds (S : System World Obs Boundary) : Prop :=
  ∀ current world, current ≠ S.required world →
    S.revise current (S.observe world) = S.required world

theorem exact_update
    (S : System World Obs Boundary)
    (hdetect : S.DetectsMismatch)
    (hsuccess : S.RevisionSucceeds)
    (hstable : S.RejectsFalseAlarm)
    (current : Boundary) (world : World) :
    S.update current world = S.required world := by
  by_cases h : current = S.required world
  · unfold update
    rw [hstable current world h]
    exact h
  · unfold update
    rw [hdetect current world h]
    simp
    exact hsuccess current world h

/--
At any fixed retained boundary, exact reality correction makes the observation
sufficient to determine the required boundary.
-/
theorem observation_sufficient
    (S : System World Obs Boundary)
    (hdetect : S.DetectsMismatch)
    (hsuccess : S.RevisionSucceeds)
    (hstable : S.RejectsFalseAlarm)
    (current : Boundary) :
    Sufficient S.observe S.required := by
  let post : Obs → Boundary := fun obs =>
    if S.reopen current obs then S.revise current obs else current
  refine ⟨post, ?_⟩
  funext world
  symm
  exact S.exact_update hdetect hsuccess hstable current world

/-- Boundary trajectory under an external sequence of reality states. -/
def trajectory
    (S : System World Obs Boundary)
    (initial : Boundary)
    (reality : ℕ → World) : ℕ → Boundary
  | 0 => initial
  | n + 1 => S.update (trajectory S initial reality n) (reality n)

@[simp] theorem trajectory_zero
    (S : System World Obs Boundary)
    (initial : Boundary) (reality : ℕ → World) :
    S.trajectory initial reality 0 = initial :=
  rfl

@[simp] theorem trajectory_succ
    (S : System World Obs Boundary)
    (initial : Boundary) (reality : ℕ → World) (n : ℕ) :
    S.trajectory initial reality (n + 1) =
      S.update (S.trajectory initial reality n) (reality n) :=
  rfl

/--
Under exact correction conditions, every completed update tracks the requirement
of the reality state just observed.
-/
theorem trajectory_tracks_reality
    (S : System World Obs Boundary)
    (hdetect : S.DetectsMismatch)
    (hsuccess : S.RevisionSucceeds)
    (hstable : S.RejectsFalseAlarm)
    (initial : Boundary)
    (reality : ℕ → World)
    (n : ℕ) :
    S.trajectory initial reality (n + 1) = S.required (reality n) := by
  rw [trajectory_succ]
  exact S.exact_update hdetect hsuccess hstable
    (S.trajectory initial reality n) (reality n)

/--
If reality's required boundary stabilizes after N, the revision trajectory
tracks that stable target after every subsequent observation.
-/
theorem tracks_stable_requirement
    (S : System World Obs Boundary)
    (hdetect : S.DetectsMismatch)
    (hsuccess : S.RevisionSucceeds)
    (hstable : S.RejectsFalseAlarm)
    (initial : Boundary)
    (reality : ℕ → World)
    (target : Boundary)
    (N : ℕ)
    (hreq : ∀ n, N ≤ n → S.required (reality n) = target) :
    ∀ n, N ≤ n →
      S.trajectory initial reality (n + 1) = target := by
  intro n hn
  rw [S.trajectory_tracks_reality hdetect hsuccess hstable initial reality n]
  exact hreq n hn

end System
end IteratedReopening
end DistinctionSelfReference
