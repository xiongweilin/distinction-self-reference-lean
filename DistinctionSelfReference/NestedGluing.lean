import Mathlib.Data.Finset.Max
import DistinctionSelfReference.LocalGlobal

namespace DistinctionSelfReference
namespace NestedGluing

open LocalGlobal

universe u v

namespace ConstraintFamily

variable {Index : Type u} {Global : Type v}

/--
A nested constraint family becomes stronger as the index increases.
A witness for a stronger constraint therefore satisfies every weaker one.
-/
def Nested [LE Index] (C : ConstraintFamily Index Global) : Prop :=
  ∀ ⦃i j⦄, i ≤ j → ∀ g, C.holds j g → C.holds i g

/--
Finite nonempty linearly ordered local constraints glue globally when they are
nested. Local satisfiability supplies a witness for the strongest constraint,
and nesting propagates that witness to every weaker constraint.
-/
theorem globallySatisfiable_of_locallySatisfiable_of_nested
    [Fintype Index] [Nonempty Index] [LinearOrder Index]
    (C : ConstraintFamily Index Global)
    (hlocal : C.LocallySatisfiable)
    (hnested : C.Nested) :
    C.GloballySatisfiable := by
  let m : Index := Finset.univ.max' Finset.univ_nonempty
  rcases hlocal m with ⟨g, hgm⟩
  refine ⟨g, ?_⟩
  intro i
  apply hnested (Finset.le_max' Finset.univ i (Finset.mem_univ i)) g hgm

/--
Under the same nesting condition, pairwise compatibility is not needed:
individual local satisfiability already suffices.
-/
theorem pairwise_redundant_under_nesting
    [Fintype Index] [Nonempty Index] [LinearOrder Index]
    (C : ConstraintFamily Index Global)
    (hlocal : C.LocallySatisfiable)
    (hnested : C.Nested) :
    C.PairwiseSatisfiable := by
  exact C.pairwiseSatisfiable_of_globallySatisfiable
    (C.globallySatisfiable_of_locallySatisfiable_of_nested hlocal hnested)

end ConstraintFamily

/-- A concrete nested Boolean family with a genuine strongest constraint. -/
inductive Level
  | weak
  | strong
  deriving DecidableEq, Repr

instance : LinearOrder Level where
  le
    | .weak, _ => True
    | .strong, .strong => True
    | .strong, .weak => False
  le_refl x := by cases x <;> trivial
  le_trans a b c := by
    cases a <;> cases b <;> cases c <;> simp_all
  le_antisymm a b := by
    cases a <;> cases b <;> simp_all
  le_total a b := by
    cases a <;> cases b <;> simp_all
  decidableLE a b := by
    cases a <;> cases b <;> infer_instance
  max a b := if a ≤ b then b else a
  max_def a b := by
    by_cases h : a ≤ b <;> simp [h]
  min a b := if a ≤ b then a else b
  min_def a b := by
    by_cases h : a ≤ b <;> simp [h]

instance : Fintype Level where
  elems := {.weak, .strong}
  complete := by intro x; cases x <;> simp

def nestedBool : ConstraintFamily Level Bool where
  holds
    | .weak, _ => True
    | .strong, b => b = true

theorem nestedBool_local :
    nestedBool.LocallySatisfiable := by
  intro i
  cases i with
  | weak => exact ⟨false, True.intro⟩
  | strong => exact ⟨true, rfl⟩

theorem nestedBool_nested :
    nestedBool.Nested := by
  intro i j hij g hj
  cases i <;> cases j <;> simp_all [nestedBool]

theorem nestedBool_global :
    nestedBool.GloballySatisfiable :=
  nestedBool.globallySatisfiable_of_locallySatisfiable_of_nested
    nestedBool_local nestedBool_nested

end NestedGluing
end DistinctionSelfReference
