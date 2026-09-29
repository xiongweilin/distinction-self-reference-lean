import DistinctionSelfReference.Recovery

namespace DistinctionSelfReference
namespace Purposeful

open Viability
open Recovery

universe u v

/-- Dynamics before any action-relevant direction is chosen. -/
structure Dynamics (State : Type u) (Action : Type v) where
  step : State → Action → State

/--
A minimal functional purpose: some states are action-relevantly acceptable,
and at least one acceptable / unacceptable distinction actually exists.
-/
structure Purpose (State : Type u) where
  acceptable : Set State
  nontrivial : ∃ good bad, good ∈ acceptable ∧ bad ∉ acceptable

namespace Dynamics

variable {State : Type u} {Action : Type v}

/-- Turn bare dynamics into a controlled system by supplying a purpose. -/
def withPurpose (D : Dynamics State Action) (P : Purpose State) :
    ControlledSystem State Action where
  step := D.step
  safe := P.acceptable

/-- Purpose refinement: P is at least as demanding as Q. -/
def PurposeRefines (P Q : Purpose State) : Prop :=
  P.acceptable ⊆ Q.acceptable

/--
Relaxing the purpose cannot destroy viability: every state viable under a
stricter acceptable set remains viable under a weaker one.
-/
theorem kernel_mono_purpose
    (D : Dynamics State Action)
    {P Q : Purpose State}
    (hPQ : PurposeRefines P Q) :
    (D.withPurpose P).kernel ⊆ (D.withPurpose Q).kernel := by
  let X : Set State := (D.withPurpose P).kernel
  have hpost : X ⊆ (D.withPurpose Q).viabilityStep X := by
    intro s hs
    have hsafeP := (D.withPurpose P).kernel_subset_safe hs
    rcases (D.withPurpose P).viable_has_viable_action hs with ⟨a, hnext⟩
    exact ⟨hPQ hsafeP, a, hnext⟩
  exact (D.withPurpose Q).subset_kernel_of_postfixed X hpost

/-- Finite action execution is independent of which purpose labels the dynamics. -/
theorem run_withPurpose_eq
    (D : Dynamics State Action)
    (P Q : Purpose State)
    (s : State) (plan : List Action) :
    run (D.withPurpose P) s plan = run (D.withPurpose Q) s plan := by
  induction plan generalizing s with
  | nil => rfl
  | cons a plan ih =>
      simp only [run_cons, withPurpose]
      exact ih (D.step s a)

/-- Relaxing purpose also cannot destroy recoverability to viability. -/
theorem recoverable_mono_purpose
    (D : Dynamics State Action)
    {P Q : Purpose State}
    (hPQ : PurposeRefines P Q)
    {s : State}
    (hs : Recoverable (D.withPurpose P) s) :
    Recoverable (D.withPurpose Q) s := by
  rcases hs with ⟨plan, hplan⟩
  refine ⟨plan, ?_⟩
  rw [← D.run_withPurpose_eq P Q s plan]
  exact D.kernel_mono_purpose hPQ hplan

end Dynamics

/-- Bare Boolean self-loop dynamics: action structure alone contains no direction. -/
def boolSelfLoop : Dynamics Bool Unit where
  step b _ := b

def preferTrue : Purpose Bool where
  acceptable := { b | b = true }
  nontrivial := ⟨true, false, rfl, by
    intro h
    exact Bool.false_eq_true_eq_False h⟩

def preferFalse : Purpose Bool where
  acceptable := { b | b = false }
  nontrivial := ⟨false, true, rfl, by
    intro h
    exact Bool.true_eq_false_eq_False h⟩

theorem true_viable_under_preferTrue :
    true ∈ (boolSelfLoop.withPurpose preferTrue).kernel := by
  let X : Set Bool := { b | b = true }
  have hpost : X ⊆ (boolSelfLoop.withPurpose preferTrue).viabilityStep X := by
    intro b hb
    change b = true at hb
    subst b
    exact ⟨rfl, Unit.unit, rfl⟩
  exact (boolSelfLoop.withPurpose preferTrue).subset_kernel_of_postfixed X hpost rfl

theorem true_not_viable_under_preferFalse :
    true ∉ (boolSelfLoop.withPurpose preferFalse).kernel := by
  intro h
  have hs := (boolSelfLoop.withPurpose preferFalse).kernel_subset_safe h
  change true = false at hs
  exact Bool.true_eq_false_eq_False hs

theorem false_viable_under_preferFalse :
    false ∈ (boolSelfLoop.withPurpose preferFalse).kernel := by
  let X : Set Bool := { b | b = false }
  have hpost : X ⊆ (boolSelfLoop.withPurpose preferFalse).viabilityStep X := by
    intro b hb
    change b = false at hb
    subst b
    exact ⟨rfl, Unit.unit, rfl⟩
  exact (boolSelfLoop.withPurpose preferFalse).subset_kernel_of_postfixed X hpost rfl

theorem false_not_viable_under_preferTrue :
    false ∉ (boolSelfLoop.withPurpose preferTrue).kernel := by
  intro h
  have hs := (boolSelfLoop.withPurpose preferTrue).kernel_subset_safe h
  change false = true at hs
  exact Bool.false_eq_true_eq_False hs

/--
The same action dynamics can induce different viability judgments solely from
the added action-relevant direction.
-/
theorem purpose_changes_viability :
    true ∈ (boolSelfLoop.withPurpose preferTrue).kernel ∧
      true ∉ (boolSelfLoop.withPurpose preferFalse).kernel ∧
      false ∈ (boolSelfLoop.withPurpose preferFalse).kernel ∧
      false ∉ (boolSelfLoop.withPurpose preferTrue).kernel := by
  exact ⟨true_viable_under_preferTrue, true_not_viable_under_preferFalse,
    false_viable_under_preferFalse, false_not_viable_under_preferTrue⟩

end Purposeful
end DistinctionSelfReference
