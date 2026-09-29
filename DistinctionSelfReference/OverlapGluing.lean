import Mathlib.Data.Bool.Basic
import DistinctionSelfReference.LocalGlobal
import DistinctionSelfReference.NestedGluing

namespace DistinctionSelfReference
namespace OverlapGluing

open LocalGlobal

universe u v w

/--
A family of local patches. Each patch specifies values only on its own scope.
The local function is total for convenience; values outside the scope are ignored.
-/
structure PatchFamily (Index : Type u) (Var : Type v) (Value : Type w) where
  scope : Index → Set Var
  assign : Index → Var → Value

namespace PatchFamily

variable {Index : Type u} {Var : Type v} {Value : Type w}

/-- Every variable occurs in at least one local patch. -/
def Covers (P : PatchFamily Index Var Value) : Prop :=
  ∀ x, ∃ i, x ∈ P.scope i

/-- Local patches agree wherever their scopes overlap. -/
def Compatible (P : PatchFamily Index Var Value) : Prop :=
  ∀ i j x, x ∈ P.scope i → x ∈ P.scope j →
    P.assign i x = P.assign j x

/-- Each patch induces a constraint on a possible global assignment. -/
def asConstraints (P : PatchFamily Index Var Value) :
    ConstraintFamily Index (Var → Value) where
  holds i g := ∀ x, x ∈ P.scope i → g x = P.assign i x

/--
Cover + pairwise agreement on actual overlaps is sufficient for a global
assignment extending every patch.
-/
theorem globallySatisfiable_of_covers_of_compatible
    (P : PatchFamily Index Var Value)
    (hcover : P.Covers)
    (hcompat : P.Compatible) :
    P.asConstraints.GloballySatisfiable := by
  classical
  choose pick hpick using hcover
  let g : Var → Value := fun x => P.assign (pick x) x
  refine ⟨g, ?_⟩
  intro i x hx
  exact hcompat (pick x) i x (hpick x) hx

theorem locallySatisfiable_of_covers_of_compatible
    (P : PatchFamily Index Var Value)
    (hcover : P.Covers)
    (hcompat : P.Compatible) :
    P.asConstraints.LocallySatisfiable :=
  P.asConstraints.locallySatisfiable_of_globallySatisfiable
    (P.globallySatisfiable_of_covers_of_compatible hcover hcompat)

end PatchFamily

/--
Two independent Boolean patches: one controls the false coordinate and the
other controls the true coordinate.
-/
def independentBool : PatchFamily Bool Bool Bool where
  scope i x := x = i
  assign i _ := i

theorem independentBool_covers :
    independentBool.Covers := by
  intro x
  exact ⟨x, rfl⟩

theorem independentBool_compatible :
    independentBool.Compatible := by
  intro i j x hxi hxj
  change x = i at hxi
  change x = j at hxj
  subst i
  subst j
  rfl

theorem independentBool_global :
    independentBool.asConstraints.GloballySatisfiable :=
  independentBool.globallySatisfiable_of_covers_of_compatible
    independentBool_covers independentBool_compatible

/-- Overlap gluing does not require the stronger nested condition. -/
theorem independentBool_not_nested :
    ¬ NestedGluing.Nested independentBool.asConstraints := by
  intro hnested
  let g : Bool → Bool := fun _ => true
  have hstrong : independentBool.asConstraints.holds true g := by
    intro x hx
    change x = true at hx
    subst x
    rfl
  have hweak := hnested (show false ≤ true by decide) g hstrong
  have hfalse := hweak false rfl
  exact Bool.true_eq_false_eq_False hfalse

end OverlapGluing
end DistinctionSelfReference
