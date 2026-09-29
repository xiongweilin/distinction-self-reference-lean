namespace DistinctionSelfReference
namespace LocalGlobal

universe u v

/--
A family of local constraints on possible global states.
-/
structure ConstraintFamily (Index : Type u) (Global : Type v) where
  holds : Index → Global → Prop

namespace ConstraintFamily

variable {Index : Type u} {Global : Type v}

def LocallySatisfiable (C : ConstraintFamily Index Global) : Prop :=
  ∀ i, ∃ g, C.holds i g

def GloballySatisfiable (C : ConstraintFamily Index Global) : Prop :=
  ∃ g, ∀ i, C.holds i g

/-- A global witness always supplies a witness for each local constraint. -/
theorem locallySatisfiable_of_globallySatisfiable
    (C : ConstraintFamily Index Global)
    (h : C.GloballySatisfiable) :
    C.LocallySatisfiable := by
  rcases h with ⟨g, hg⟩
  intro i
  exact ⟨g, hg i⟩

end ConstraintFamily

/--
The smallest explicit obstruction: each of two constraints is satisfiable on
its own, but no single global state satisfies both.
-/
inductive Opposed
  | requireFalse
  | requireTrue
  deriving DecidableEq, Repr

def opposedBool : ConstraintFamily Opposed Bool where
  holds
    | .requireFalse, b => b = false
    | .requireTrue, b => b = true

theorem opposedBool_locallySatisfiable :
    opposedBool.LocallySatisfiable := by
  intro i
  cases i with
  | requireFalse => exact ⟨false, rfl⟩
  | requireTrue => exact ⟨true, rfl⟩

theorem opposedBool_not_globallySatisfiable :
    ¬ opposedBool.GloballySatisfiable := by
  rintro ⟨b, hb⟩
  have hf : b = false := hb .requireFalse
  have ht : b = true := hb .requireTrue
  cases b <;> simp_all

/--
Therefore local satisfiability alone cannot justify global composition.
-/
theorem local_does_not_imply_global :
    ∃ (Index Global : Type),
      ∃ C : ConstraintFamily Index Global,
        C.LocallySatisfiable ∧ ¬ C.GloballySatisfiable := by
  exact ⟨Opposed, Bool, opposedBool,
    opposedBool_locallySatisfiable,
    opposedBool_not_globallySatisfiable⟩

end LocalGlobal
end DistinctionSelfReference
