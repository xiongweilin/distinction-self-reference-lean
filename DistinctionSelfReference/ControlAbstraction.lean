import DistinctionSelfReference.Recovery
import DistinctionSelfReference.InformationOrder

namespace DistinctionSelfReference
namespace ControlAbstraction

open Viability
open Recovery
open InformationOrder

universe u v w

/--
A deterministic abstraction between controlled systems with the same action type.
It preserves the action-labelled dynamics exactly, while safety preservation
and reflection are tracked as separate conditions.
-/
structure Hom
    {Concrete : Type u} {Abstract : Type v} {Action : Type w}
    (C : ControlledSystem Concrete Action)
    (A : ControlledSystem Abstract Action) where
  map : Concrete → Abstract
  step_commute : ∀ s a, map (C.step s a) = A.step (map s) a

namespace Hom

variable
  {Concrete : Type u} {Abstract : Type v} {Action : Type w}
  {C : ControlledSystem Concrete Action}
  {A : ControlledSystem Abstract Action}

def SafePreserving (h : Hom C A) : Prop :=
  ∀ ⦃s⦄, s ∈ C.safe → h.map s ∈ A.safe

def SafeReflecting (h : Hom C A) : Prop :=
  ∀ ⦃s⦄, h.map s ∈ A.safe → s ∈ C.safe

/-- The concrete state identity representation refines every abstraction map. -/
theorem information_coarsening (h : Hom C A) :
    Refines (fun s : Concrete => s) h.map := by
  exact ⟨h.map, rfl⟩

/-- A finite action plan commutes with a dynamics-preserving abstraction. -/
theorem run_commute
    (h : Hom C A) (s : Concrete) (plan : List Action) :
    h.map (run C s plan) = run A (h.map s) plan := by
  induction plan generalizing s with
  | nil => rfl
  | cons a plan ih =>
      simp only [run_cons]
      rw [h.step_commute]
      exact ih (C.step s a)

/--
Safety preservation is sufficient for viability to map forward through an
information-losing abstraction.
-/
theorem map_kernel_of_safePreserving
    (h : Hom C A)
    (hsafe : h.SafePreserving)
    {s : Concrete}
    (hs : s ∈ C.kernel) :
    h.map s ∈ A.kernel := by
  let X : Set Abstract := { t | ∃ s, s ∈ C.kernel ∧ h.map s = t }
  have hpost : X ⊆ A.viabilityStep X := by
    intro t ht
    rcases ht with ⟨s0, hs0, rfl⟩
    have hsafe0 : s0 ∈ C.safe := C.kernel_subset_safe hs0
    rcases C.viable_has_viable_action hs0 with ⟨a, hnext⟩
    refine ⟨hsafe hsafe0, a, ?_⟩
    refine ⟨C.step s0 a, hnext, ?_⟩
    exact h.step_commute s0 a
  apply A.subset_kernel_of_postfixed X hpost
  exact ⟨s, hs, rfl⟩

/--
Safety reflection is sufficient for viability to reflect back from the
abstract system to every concrete state in the fiber.
-/
theorem mem_kernel_of_map_mem_kernel_of_safeReflecting
    (h : Hom C A)
    (hsafe : h.SafeReflecting)
    {s : Concrete}
    (hs : h.map s ∈ A.kernel) :
    s ∈ C.kernel := by
  let X : Set Concrete := { s0 | h.map s0 ∈ A.kernel }
  have hpost : X ⊆ C.viabilityStep X := by
    intro s0 hs0
    have hu := (A.mem_kernel_iff (h.map s0)).mp hs0
    rcases hu with ⟨hasafe, a, hnext⟩
    refine ⟨hsafe hasafe, a, ?_⟩
    change h.map (C.step s0 a) ∈ A.kernel
    rw [h.step_commute]
    exact hnext
  exact C.subset_kernel_of_postfixed X hpost hs

/-- With safety preserved and reflected, viability is exact under abstraction. -/
theorem mem_kernel_iff_map_mem_kernel
    (h : Hom C A)
    (hpres : h.SafePreserving)
    (hrefl : h.SafeReflecting)
    (s : Concrete) :
    s ∈ C.kernel ↔ h.map s ∈ A.kernel := by
  constructor
  · exact h.map_kernel_of_safePreserving hpres
  · exact h.mem_kernel_of_map_mem_kernel_of_safeReflecting hrefl

/-- Forward viability preservation lifts to finite-plan recoverability. -/
theorem map_recoverable_of_safePreserving
    (h : Hom C A)
    (hsafe : h.SafePreserving)
    {s : Concrete}
    (hs : Recoverable C s) :
    Recoverable A (h.map s) := by
  rcases hs with ⟨plan, hplan⟩
  refine ⟨plan, ?_⟩
  rw [← h.run_commute s plan]
  exact h.map_kernel_of_safePreserving hsafe hplan

/-- Safety reflection also reflects finite-plan recoverability. -/
theorem recoverable_of_map_recoverable_of_safeReflecting
    (h : Hom C A)
    (hsafe : h.SafeReflecting)
    {s : Concrete}
    (hs : Recoverable A (h.map s)) :
    Recoverable C s := by
  rcases hs with ⟨plan, hplan⟩
  refine ⟨plan, ?_⟩
  apply h.mem_kernel_of_map_mem_kernel_of_safeReflecting hsafe
  rw [h.run_commute]
  exact hplan

/--
When safety is both preserved and reflected, recoverability is exact under
the abstraction as well.
-/
theorem recoverable_iff_map_recoverable
    (h : Hom C A)
    (hpres : h.SafePreserving)
    (hrefl : h.SafeReflecting)
    (s : Concrete) :
    Recoverable C s ↔ Recoverable A (h.map s) := by
  constructor
  · exact h.map_recoverable_of_safePreserving hpres
  · exact h.recoverable_of_map_recoverable_of_safeReflecting hrefl

end Hom

/-- A concrete two-state system whose bad state can never become safe. -/
inductive ConcreteState
  | good
  | bad
  deriving DecidableEq, Repr

inductive Act
  | stay
  deriving DecidableEq, Repr

def concrete : ControlledSystem ConcreteState Act where
  step s _ := s
  safe
    | .good => True
    | .bad => False

/-- The coarse one-state abstraction forgets the good/bad distinction. -/
def abstract : ControlledSystem Unit Act where
  step _ _ := Unit.unit
  safe _ := True

def collapse : Hom concrete abstract where
  map _ := Unit.unit
  step_commute := by intro s a; cases s <;> cases a <;> rfl

theorem collapse_safePreserving :
    collapse.SafePreserving := by
  intro s hs
  trivial

theorem collapse_not_safeReflecting :
    ¬ collapse.SafeReflecting := by
  intro h
  exact h (s := ConcreteState.bad) True.intro

theorem abstract_viable :
    Unit.unit ∈ abstract.kernel := by
  let X : Set Unit := Set.univ
  have hpost : X ⊆ abstract.viabilityStep X := by
    intro s hs
    exact ⟨True.intro, Act.stay, Set.mem_univ _⟩
  exact abstract.subset_kernel_of_postfixed X hpost (Set.mem_univ _)

theorem bad_not_viable :
    ConcreteState.bad ∉ concrete.kernel := by
  intro h
  exact concrete.kernel_subset_safe h

theorem bad_run (plan : List Act) :
    run concrete ConcreteState.bad plan = ConcreteState.bad := by
  induction plan with
  | nil => rfl
  | cons a plan ih =>
      cases a
      simpa [concrete] using ih

theorem bad_not_recoverable :
    ¬ Recoverable concrete ConcreteState.bad := by
  rintro ⟨plan, hplan⟩
  rw [bad_run] at hplan
  exact bad_not_viable hplan

theorem abstract_recoverable :
    Recoverable abstract Unit.unit :=
  recoverable_of_mem_kernel abstract abstract_viable

/--
Information loss can create false positive viability when safety reflection
is absent.
-/
theorem coarse_viability_false_positive :
    collapse.map ConcreteState.bad ∈ abstract.kernel ∧
      ConcreteState.bad ∉ concrete.kernel := by
  exact ⟨abstract_viable, bad_not_viable⟩

/-- The same coarse abstraction can also create false positive recoverability. -/
theorem coarse_recovery_false_positive :
    Recoverable abstract (collapse.map ConcreteState.bad) ∧
      ¬ Recoverable concrete ConcreteState.bad := by
  exact ⟨abstract_recoverable, bad_not_recoverable⟩

end ControlAbstraction
end DistinctionSelfReference
