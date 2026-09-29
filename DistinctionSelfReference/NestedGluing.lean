import Mathlib.Data.Bool.Basic
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

/--
A concrete nested Boolean-indexed family.
false is the weak constraint; true is the stronger constraint.
-/
def nestedBool : ConstraintFamily Bool Bool where
  holds
    | false, _ => True
    | true, b => b = true

theorem nestedBool_local :
    nestedBool.LocallySatisfiable := by
  intro i
  cases i with
  | false => exact ⟨false, True.intro⟩
  | true => exact ⟨true, rfl⟩

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
