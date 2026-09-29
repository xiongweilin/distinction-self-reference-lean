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

def PairwiseSatisfiable (C : ConstraintFamily Index Global) : Prop :=
  ∀ ⦃i j⦄, i ≠ j → ∃ g, C.holds i g ∧ C.holds j g

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

/-- A global witness also witnesses every pair of local constraints. -/
theorem pairwiseSatisfiable_of_globallySatisfiable
    (C : ConstraintFamily Index Global)
    (h : C.GloballySatisfiable) :
    C.PairwiseSatisfiable := by
  rcases h with ⟨g, hg⟩
  intro i j _
  exact ⟨g, hg i, hg j⟩

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

/--
Three constraints whose every distinct pair is jointly satisfiable:
x = true, y = true, and x ≠ y.
All three together are inconsistent.
-/
inductive Triangle
  | requireX
  | requireY
  | requireDifferent
  deriving DecidableEq, Repr

def triangleBool : ConstraintFamily Triangle (Bool × Bool) where
  holds
    | .requireX, g => g.1 = true
    | .requireY, g => g.2 = true
    | .requireDifferent, g => g.1 ≠ g.2

theorem triangleBool_pairwiseSatisfiable :
    triangleBool.PairwiseSatisfiable := by
  intro i j hij
  cases i with
  | requireX =>
      cases j with
      | requireX => exact (hij rfl).elim
      | requireY => exact ⟨(true, true), rfl, rfl⟩
      | requireDifferent =>
          exact ⟨(true, false), rfl, by decide⟩
  | requireY =>
      cases j with
      | requireX => exact ⟨(true, true), rfl, rfl⟩
      | requireY => exact (hij rfl).elim
      | requireDifferent =>
          exact ⟨(false, true), rfl, by decide⟩
  | requireDifferent =>
      cases j with
      | requireX => exact ⟨(true, false), by simp, rfl⟩
      | requireY => exact ⟨(false, true), by simp, rfl⟩
      | requireDifferent => exact (hij rfl).elim

theorem triangleBool_not_globallySatisfiable :
    ¬ triangleBool.GloballySatisfiable := by
  rintro ⟨⟨x, y⟩, h⟩
  have hx := h .requireX
  have hy := h .requireY
  have hd := h .requireDifferent
  change x = true at hx
  change y = true at hy
  change x ≠ y at hd
  subst x
  subst y
  exact hd rfl

/--
Even pairwise compatibility of all local constraints does not, by itself,
guarantee a global witness.
-/
theorem pairwise_does_not_imply_global :
    ∃ (Index Global : Type),
      ∃ C : ConstraintFamily Index Global,
        C.PairwiseSatisfiable ∧ ¬ C.GloballySatisfiable := by
  exact ⟨Triangle, Bool × Bool, triangleBool,
    triangleBool_pairwiseSatisfiable,
    triangleBool_not_globallySatisfiable⟩

end LocalGlobal
end DistinctionSelfReference
