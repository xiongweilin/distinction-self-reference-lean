import Mathlib.Data.Finset.Max
import DistinctionSelfReference.LocalGlobal

namespace DistinctionSelfReference
namespace NestedGluing

open LocalGlobal

universe u v

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
    (hnested : Nested C) :
    C.GloballySatisfiable := by
  let i0 : Index := Classical.choice (inferInstance : Nonempty Index)
  have huniv : (Finset.univ : Finset Index).Nonempty :=
    ⟨i0, Finset.mem_univ i0⟩
  let m : Index := Finset.univ.max' huniv
  rcases hlocal m with ⟨g, hgm⟩
  refine ⟨g, ?_⟩
  intro i
  exact hnested (Finset.le_max' Finset.univ i (Finset.mem_univ i)) g hgm

/--
Under nesting, pairwise compatibility becomes redundant: local
satisfiability already yields one common global witness.
-/
theorem pairwise_redundant_under_nesting
    [Fintype Index] [Nonempty Index] [LinearOrder Index]
    (C : ConstraintFamily Index Global)
    (hlocal : C.LocallySatisfiable)
    (hnested : Nested C) :
    C.PairwiseSatisfiable := by
  exact C.pairwiseSatisfiable_of_globallySatisfiable
    (globallySatisfiable_of_locallySatisfiable_of_nested C hlocal hnested)

end NestedGluing
end DistinctionSelfReference
