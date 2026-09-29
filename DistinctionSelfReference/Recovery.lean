import DistinctionSelfReference.Viability

namespace DistinctionSelfReference
namespace Recovery

universe u v

open Viability

namespace ControlledSystem

variable {State : Type u} {Action : Type v}

/-- Execute a finite action plan. -/
def run (C : ControlledSystem State Action) (s : State) : List Action → State
  | [] => s
  | a :: plan => C.run (C.step s a) plan

@[simp] theorem run_nil
    (C : ControlledSystem State Action) (s : State) :
    C.run s [] = s :=
  rfl

@[simp] theorem run_cons
    (C : ControlledSystem State Action)
    (s : State) (a : Action) (plan : List Action) :
    C.run s (a :: plan) = C.run (C.step s a) plan :=
  rfl

/-- A state is recoverable to a target when some finite action plan reaches it. -/
def RecoverableTo
    (C : ControlledSystem State Action) (target : Set State) (s : State) : Prop :=
  ∃ plan : List Action, C.run s plan ∈ target

/-- Recoverability to the viability kernel. -/
def Recoverable
    (C : ControlledSystem State Action) (s : State) : Prop :=
  C.RecoverableTo C.kernel s

/-- Failure of all finite recovery plans back to viability. -/
def Irrecoverable
    (C : ControlledSystem State Action) (s : State) : Prop :=
  ¬ C.Recoverable s

/-- Every viable state is trivially recoverable by the empty plan. -/
theorem recoverable_of_mem_kernel
    (C : ControlledSystem State Action) {s : State}
    (hs : s ∈ C.kernel) :
    C.Recoverable s :=
  ⟨[], hs⟩

/-- A one-step predecessor of a recoverable state is recoverable. -/
theorem recoverable_of_step
    (C : ControlledSystem State Action)
    {s : State} (a : Action)
    (hnext : C.Recoverable (C.step s a)) :
    C.Recoverable s := by
  rcases hnext with ⟨plan, hplan⟩
  exact ⟨a :: plan, hplan⟩

/-- Irrecoverable states lie outside the viability kernel. -/
theorem irrecoverable_not_mem_kernel
    (C : ControlledSystem State Action) {s : State}
    (h : C.Irrecoverable s) :
    s ∉ C.kernel := by
  intro hs
  exact h (C.recoverable_of_mem_kernel hs)

/--
Viability is strictly stronger than finite recoverability in general:
recovery may pass through nonviable states before re-entering the kernel.
This theorem records the guaranteed inclusion only.
-/
theorem kernel_subset_recoverable
    (C : ControlledSystem State Action) :
    C.kernel ⊆ { s | C.Recoverable s } := by
  intro s hs
  exact C.recoverable_of_mem_kernel hs

end ControlledSystem
end Recovery
end DistinctionSelfReference
