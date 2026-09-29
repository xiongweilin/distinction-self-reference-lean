import DistinctionSelfReference.Viability

namespace DistinctionSelfReference
namespace Recovery

universe u v

open Viability

variable {State : Type u} {Action : Type v}

/-- Execute a finite action plan. -/
def run (C : ControlledSystem State Action) (s : State) : List Action → State
  | [] => s
  | a :: plan => run C (C.step s a) plan

@[simp] theorem run_nil
    (C : ControlledSystem State Action) (s : State) :
    run C s [] = s :=
  rfl

@[simp] theorem run_cons
    (C : ControlledSystem State Action)
    (s : State) (a : Action) (plan : List Action) :
    run C s (a :: plan) = run C (C.step s a) plan :=
  rfl

/-- A state is recoverable to a target when some finite action plan reaches it. -/
def RecoverableTo
    (C : ControlledSystem State Action) (target : Set State) (s : State) : Prop :=
  ∃ plan : List Action, run C s plan ∈ target

/-- Recoverability to the viability kernel. -/
def Recoverable
    (C : ControlledSystem State Action) (s : State) : Prop :=
  RecoverableTo C C.kernel s

/-- Failure of all finite recovery plans back to viability. -/
def Irrecoverable
    (C : ControlledSystem State Action) (s : State) : Prop :=
  ¬ Recoverable C s

/-- Every viable state is trivially recoverable by the empty plan. -/
theorem recoverable_of_mem_kernel
    (C : ControlledSystem State Action) {s : State}
    (hs : s ∈ C.kernel) :
    Recoverable C s :=
  ⟨[], hs⟩

/-- A one-step predecessor of a recoverable state is recoverable. -/
theorem recoverable_of_step
    (C : ControlledSystem State Action)
    {s : State} (a : Action)
    (hnext : Recoverable C (C.step s a)) :
    Recoverable C s := by
  rcases hnext with ⟨plan, hplan⟩
  exact ⟨a :: plan, hplan⟩

/-- Irrecoverable states lie outside the viability kernel. -/
theorem irrecoverable_not_mem_kernel
    (C : ControlledSystem State Action) {s : State}
    (h : Irrecoverable C s) :
    s ∉ C.kernel := by
  intro hs
  exact h (recoverable_of_mem_kernel C hs)

/--
Viability is always contained in finite recoverability to viability.
The converse needs extra conditions and is not assumed.
-/
theorem kernel_subset_recoverable
    (C : ControlledSystem State Action) :
    C.kernel ⊆ { s | Recoverable C s } := by
  intro s hs
  exact recoverable_of_mem_kernel C hs

end Recovery
end DistinctionSelfReference
