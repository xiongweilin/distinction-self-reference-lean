import DistinctionSelfReference.CapabilityOrder

namespace DistinctionSelfReference
namespace ChangingEvaluator

universe u

/-- A time-local evaluator is only a binary improvement relation. -/
structure Evaluator (State : Type u) where
  better : State → State → Prop

def LocalImprovement
    {State : Type u}
    (evaluators : Nat → Evaluator State)
    (trajectory : Nat → State) : Prop :=
  ∀ n, (evaluators n).better (trajectory n) (trajectory (n + 1))

/--
Every local evaluator is coherent with one global relation when all local
improvement edges are also global improvement edges.
-/
def CoherentWithGlobal
    {State : Type u}
    (evaluators : Nat → Evaluator State)
    (global : Evaluator State) : Prop :=
  ∀ n a b, (evaluators n).better a b → global.better a b

/--
A common transitive global evaluator composes all local improvements into
endpoint improvement over every finite nonempty prefix.
-/
theorem local_to_global
    {State : Type u}
    (evaluators : Nat → Evaluator State)
    (trajectory : Nat → State)
    (global : Evaluator State)
    (hlocal : LocalImprovement evaluators trajectory)
    (hcoherent : CoherentWithGlobal evaluators global)
    (htrans : Transitive global.better) :
    ∀ n, global.better (trajectory 0) (trajectory (n + 1)) := by
  intro n
  induction n with
  | zero =>
      exact hcoherent 0 _ _ (hlocal 0)
  | succ n ih =>
      exact htrans ih
        (hcoherent (n + 1) _ _ (hlocal (n + 1)))

/--
A common potential is a stronger numerical coherence witness.
-/
def CommonPotential
    {State : Type u}
    (evaluators : Nat → Evaluator State)
    (potential : State → Nat) : Prop :=
  ∀ n a b,
    (evaluators n).better a b →
    potential a < potential b

theorem potential_increases_each_step
    {State : Type u}
    (evaluators : Nat → Evaluator State)
    (trajectory : Nat → State)
    (potential : State → Nat)
    (hlocal : LocalImprovement evaluators trajectory)
    (hpotential : CommonPotential evaluators potential) :
    ∀ n, potential (trajectory n) < potential (trajectory (n + 1)) := by
  intro n
  exact hpotential n _ _ (hlocal n)

/--
Any trajectory whatsoever can be made locally improving if the evaluator is
allowed to change adversarially with the trajectory itself.
-/
def pathEvaluator
    {State : Type u}
    (trajectory : Nat → State)
    (n : Nat) :
    Evaluator State where
  better a b :=
    a = trajectory n ∧ b = trajectory (n + 1)

theorem every_path_locally_improves
    {State : Type u}
    (trajectory : Nat → State) :
    LocalImprovement (pathEvaluator trajectory) trajectory := by
  intro n
  exact ⟨rfl, rfl⟩

/-- A concrete recurrent path. -/
def toggle : Nat → Bool
  | 0 => false
  | n + 1 => !(toggle n)

theorem toggle_two_step (n : Nat) :
    toggle (n + 2) = toggle n := by
  change !(!(toggle n)) = toggle n
  cases toggle n <;> rfl

theorem toggle_locally_improves :
    LocalImprovement (pathEvaluator toggle) toggle :=
  every_path_locally_improves toggle

theorem toggle_recurrence :
    toggle 2 = toggle 0 := by
  exact toggle_two_step 0

/--
Local improvement under changing evaluators can coexist with recurrence.
Hence local improvement alone does not imply any strict global order.
-/
theorem no_irreflexive_transitive_global_extension :
    ¬ ∃ global : Evaluator Bool,
        Irreflexive global.better ∧
        Transitive global.better ∧
        CoherentWithGlobal (pathEvaluator toggle) global := by
  rintro ⟨global, hirr, htrans, hcoherent⟩
  have h01 :
      global.better (toggle 0) (toggle 1) :=
    hcoherent 0 _ _ (toggle_locally_improves 0)
  have h12 :
      global.better (toggle 1) (toggle 2) :=
    hcoherent 1 _ _ (toggle_locally_improves 1)
  have h02 := htrans h01 h12
  rw [toggle_recurrence] at h02
  exact hirr (toggle 0) h02

end ChangingEvaluator
end DistinctionSelfReference
