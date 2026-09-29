import DistinctionSelfReference.ControlAbstraction

namespace DistinctionSelfReference
namespace ControlSimulation

open Viability
open Recovery

universe u v w z

/--
A state abstraction between controlled systems whose action types may differ.
Step matching is deliberately separated into forward and backward conditions.
-/
structure StateMap
    {Concrete : Type u} {Abstract : Type v}
    {ConcreteAction : Type w} {AbstractAction : Type z}
    (C : ControlledSystem Concrete ConcreteAction)
    (A : ControlledSystem Abstract AbstractAction) where
  map : Concrete → Abstract

namespace StateMap

variable
  {Concrete : Type u} {Abstract : Type v}
  {ConcreteAction : Type w} {AbstractAction : Type z}
  {C : ControlledSystem Concrete ConcreteAction}
  {A : ControlledSystem Abstract AbstractAction}

/-- Every concrete transition can be matched abstractly. -/
def ForwardSimulates (h : StateMap C A) : Prop :=
  ∀ s a, ∃ b, h.map (C.step s a) = A.step (h.map s) b

/-- Every abstract transition can be realized concretely from each fiber state. -/
def BackwardSimulates (h : StateMap C A) : Prop :=
  ∀ s b, ∃ a, h.map (C.step s a) = A.step (h.map s) b

def SafePreserving (h : StateMap C A) : Prop :=
  ∀ ⦃s⦄, s ∈ C.safe → h.map s ∈ A.safe

def SafeReflecting (h : StateMap C A) : Prop :=
  ∀ ⦃s⦄, h.map s ∈ A.safe → s ∈ C.safe

/-- Forward simulation plus safety preservation preserves viability. -/
theorem map_kernel_of_forward
    (h : StateMap C A)
    (hstep : h.ForwardSimulates)
    (hsafe : h.SafePreserving)
    {s : Concrete}
    (hs : s ∈ C.kernel) :
    h.map s ∈ A.kernel := by
  let X : Set Abstract := { t | ∃ s0, s0 ∈ C.kernel ∧ h.map s0 = t }
  have hpost : X ⊆ A.viabilityStep X := by
    intro t ht
    rcases ht with ⟨s0, hs0, rfl⟩
    have hsafe0 : s0 ∈ C.safe := C.kernel_subset_safe hs0
    rcases C.viable_has_viable_action hs0 with ⟨a, hnext⟩
    rcases hstep s0 a with ⟨b, hmatch⟩
    refine ⟨hsafe hsafe0, b, ?_⟩
    refine ⟨C.step s0 a, hnext, hmatch⟩
  exact A.subset_kernel_of_postfixed X hpost ⟨s, hs, rfl⟩

/-- Backward simulation plus safety reflection reflects viability. -/
theorem mem_kernel_of_map_mem_kernel_of_backward
    (h : StateMap C A)
    (hstep : h.BackwardSimulates)
    (hsafe : h.SafeReflecting)
    {s : Concrete}
    (hs : h.map s ∈ A.kernel) :
    s ∈ C.kernel := by
  let X : Set Concrete := { s0 | h.map s0 ∈ A.kernel }
  have hpost : X ⊆ C.viabilityStep X := by
    intro s0 hs0
    rcases (A.mem_kernel_iff (h.map s0)).mp hs0 with ⟨hasafe, b, hnext⟩
    rcases hstep s0 b with ⟨a, hmatch⟩
    refine ⟨hsafe hasafe, a, ?_⟩
    change h.map (C.step s0 a) ∈ A.kernel
    rw [hmatch]
    exact hnext
  exact C.subset_kernel_of_postfixed X hpost hs

/-- Match an entire concrete action plan by some abstract action plan. -/
theorem match_forward_plan
    (h : StateMap C A)
    (hstep : h.ForwardSimulates)
    (s : Concrete) (plan : List ConcreteAction) :
    ∃ abstractPlan : List AbstractAction,
      h.map (run C s plan) = run A (h.map s) abstractPlan := by
  induction plan generalizing s with
  | nil => exact ⟨[], rfl⟩
  | cons a plan ih =>
      rcases hstep s a with ⟨b, hmatch⟩
      rcases ih (C.step s a) with ⟨rest, hrest⟩
      refine ⟨b :: rest, ?_⟩
      simp only [run_cons]
      calc
        h.map (run C (C.step s a) plan)
            = run A (h.map (C.step s a)) rest := hrest
        _ = run A (A.step (h.map s) b) rest := by rw [hmatch]

/-- Match an entire abstract action plan by some concrete action plan. -/
theorem match_backward_plan
    (h : StateMap C A)
    (hstep : h.BackwardSimulates)
    (s : Concrete) (plan : List AbstractAction) :
    ∃ concretePlan : List ConcreteAction,
      h.map (run C s concretePlan) = run A (h.map s) plan := by
  induction plan generalizing s with
  | nil => exact ⟨[], rfl⟩
  | cons b plan ih =>
      rcases hstep s b with ⟨a, hmatch⟩
      rcases ih (C.step s a) with ⟨rest, hrest⟩
      refine ⟨a :: rest, ?_⟩
      simp only [run_cons]
      calc
        h.map (run C (C.step s a) rest)
            = run A (h.map (C.step s a)) plan := hrest
        _ = run A (A.step (h.map s) b) plan := by rw [hmatch]

/-- Forward simulation also preserves finite-plan recoverability. -/
theorem map_recoverable_of_forward
    (h : StateMap C A)
    (hstep : h.ForwardSimulates)
    (hsafe : h.SafePreserving)
    {s : Concrete}
    (hs : Recoverable C s) :
    Recoverable A (h.map s) := by
  rcases hs with ⟨plan, hplan⟩
  rcases h.match_forward_plan hstep s plan with ⟨abstractPlan, hrun⟩
  refine ⟨abstractPlan, ?_⟩
  rw [← hrun]
  exact h.map_kernel_of_forward hstep hsafe hplan

/-- Backward simulation reflects finite-plan recoverability. -/
theorem recoverable_of_map_recoverable_of_backward
    (h : StateMap C A)
    (hstep : h.BackwardSimulates)
    (hsafe : h.SafeReflecting)
    {s : Concrete}
    (hs : Recoverable A (h.map s)) :
    Recoverable C s := by
  rcases hs with ⟨plan, hplan⟩
  rcases h.match_backward_plan hstep s plan with ⟨concretePlan, hrun⟩
  refine ⟨concretePlan, ?_⟩
  apply h.mem_kernel_of_map_mem_kernel_of_backward hstep hsafe
  rw [hrun]
  exact hplan

end StateMap

namespace FromHom

variable
  {Concrete : Type u} {Abstract : Type v} {Action : Type w}
  {C : ControlledSystem Concrete Action}
  {A : ControlledSystem Abstract Action}

/-- Every exact commuting abstraction induces the weaker state-map interface. -/
def stateMap (h : ControlAbstraction.Hom C A) : StateMap C A where
  map := h.map

theorem forward
    (h : ControlAbstraction.Hom C A) :
    (stateMap h).ForwardSimulates := by
  intro s a
  exact ⟨a, h.step_commute s a⟩

theorem backward
    (h : ControlAbstraction.Hom C A) :
    (stateMap h).BackwardSimulates := by
  intro s a
  exact ⟨a, h.step_commute s a⟩

end FromHom
end ControlSimulation
end DistinctionSelfReference
