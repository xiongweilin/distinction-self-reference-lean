import DistinctionSelfReference.RepresentationalObstruction

namespace DistinctionSelfReference
namespace WeakRepresentation

universe u v

/--
For a particular endomap, Lawvere's diagonal argument only needs the
corresponding diagonal function to be representable; full surjectivity onto
the whole function space is stronger than necessary.
-/
def DiagonalRepresentable
    {Alpha : Type u} {Beta : Type v}
    (eval : Alpha → Alpha → Beta)
    (step : Beta → Beta) : Prop :=
  ∃ a, eval a = fun x => step (eval x x)

theorem diagonalRepresentable_forces_fixed_point
    {Alpha : Type u} {Beta : Type v}
    (eval : Alpha → Alpha → Beta)
    (step : Beta → Beta)
    (hdiag : DiagonalRepresentable eval step) :
    ∃ x, step x = x := by
  rcases hdiag with ⟨a, ha⟩
  let x : Beta := eval a a
  refine ⟨x, ?_⟩
  have h := congrFun ha a
  exact h.symm

/-- Full point-surjectivity implies the weaker per-endomap diagonal condition. -/
theorem diagonalRepresentable_of_surjective
    {Alpha : Type u} {Beta : Type v}
    (eval : Alpha → Alpha → Beta)
    (heval : Function.Surjective eval)
    (step : Beta → Beta) :
    DiagonalRepresentable eval step := by
  exact heval (fun x => step (eval x x))

/--
A fixed-point-free endomap excludes exactly its own Lawvere diagonal from the
representable family, even when many other functions may remain representable.
-/
theorem fixedPointFree_forbids_diagonalRepresentation
    {Alpha : Type u} {Beta : Type v}
    (eval : Alpha → Alpha → Beta)
    (step : Beta → Beta)
    (hfree : ∀ x, step x ≠ x) :
    ¬ DiagonalRepresentable eval step := by
  intro hdiag
  rcases diagonalRepresentable_forces_fixed_point eval step hdiag with ⟨x, hx⟩
  exact hfree x hx

/-- The two-state crossing forbids its diagonal function for every evaluator. -/
theorem twoState_diagonal_unrepresentable
    {Alpha : Type u}
    (eval : Alpha → Alpha → TwoState.Side) :
    ¬ DiagonalRepresentable eval TwoState.cross := by
  exact fixedPointFree_forbids_diagonalRepresentation
    eval TwoState.cross TwoState.cross_ne_self

/-- A family of functions is represented when each member has a code. -/
def RepresentsFamily
    {Alpha : Type u} {Beta : Type v}
    (eval : Alpha → Alpha → Beta)
    (family : Set (Alpha → Beta)) : Prop :=
  ∀ ⦃f⦄, f ∈ family → ∃ a, eval a = f

/--
Representing any family that contains the relevant diagonal function is already
enough for the fixed-point argument.
-/
theorem family_containing_diagonal_forces_fixed_point
    {Alpha : Type u} {Beta : Type v}
    (eval : Alpha → Alpha → Beta)
    (family : Set (Alpha → Beta))
    (hrep : RepresentsFamily eval family)
    (step : Beta → Beta)
    (hdiag : (fun x => step (eval x x)) ∈ family) :
    ∃ x, step x = x := by
  apply diagonalRepresentable_forces_fixed_point eval step
  exact hrep hdiag

/-- A minimal partial evaluator for the two-state result type. -/
def twoStateConstantEval : Unit → Unit → TwoState.Side :=
  fun _ _ => TwoState.Side.unmarked

/-- The one-function family represented by the minimal evaluator. -/
def constantUnmarkedFamily : Set (Unit → TwoState.Side) :=
  { f | f = fun _ => TwoState.Side.unmarked }

theorem twoStateConstantEval_represents_family :
    RepresentsFamily twoStateConstantEval constantUnmarkedFamily := by
  intro f hf
  refine ⟨Unit.unit, ?_⟩
  change twoStateConstantEval Unit.unit = f
  rw [hf]
  funext x
  rfl

/--
Partial representation can coexist with the fixed-point-free two-state crossing,
provided the forbidden diagonal function is not included.
-/
theorem partial_twoState_representation_exists :
    RepresentsFamily twoStateConstantEval constantUnmarkedFamily ∧
      ¬ DiagonalRepresentable twoStateConstantEval TwoState.cross := by
  constructor
  · exact twoStateConstantEval_represents_family
  · exact twoState_diagonal_unrepresentable twoStateConstantEval

end WeakRepresentation
end DistinctionSelfReference
