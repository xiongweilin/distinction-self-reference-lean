import DistinctionSelfReference.TwoState

namespace DistinctionSelfReference
namespace GuardedLawvere

universe u v

/--
A guard-separated evaluator. The value layer is total, but only pairs satisfying
`allowed` are semantically available for evaluation. This abstracts the
definedness boundary away from the concrete `Option` representation.
-/
structure GuardedEvaluator (Alpha : Type u) (Beta : Type v) where
  allowed : Alpha → Alpha → Prop
  value : Alpha → Alpha → Beta

/--
At a represented diagonal point, availability matches self-availability of the
argument code and, whenever available, the value realizes the mapped diagonal.
-/
structure GuardedDiagonalAt
    {Alpha : Type u}
    {Beta : Type v}
    (E : GuardedEvaluator Alpha Beta)
    (step : Beta → Beta)
    (a x : Alpha) : Prop where
  allowed_iff :
    E.allowed a x ↔ E.allowed x x
  value_eq :
    E.allowed a x →
      E.value a x = step (E.value x x)

def GuardedDiagonalWitness
    {Alpha : Type u}
    {Beta : Type v}
    (E : GuardedEvaluator Alpha Beta)
    (step : Beta → Beta)
    (a : Alpha) : Prop :=
  ∀ x, GuardedDiagonalAt E step a x

def GuardedDiagonalRepresentable
    {Alpha : Type u}
    {Beta : Type v}
    (E : GuardedEvaluator Alpha Beta)
    (step : Beta → Beta) : Prop :=
  ∃ a, GuardedDiagonalWitness E step a

/--
Guarded Lawvere threshold: representation plus an open self-application guard
forces an ordinary fixed point.
-/
theorem open_self_guard_forces_fixed_point
    {Alpha : Type u}
    {Beta : Type v}
    (E : GuardedEvaluator Alpha Beta)
    (step : Beta → Beta)
    (a : Alpha)
    (hdiag : GuardedDiagonalWitness E step a)
    (hopen : E.allowed a a) :
    ∃ value, step value = value := by
  refine ⟨E.value a a, ?_⟩
  exact (hdiag a).value_eq hopen |>.symm

/--
For a fixed-point-free endomap, every guarded diagonal witness must close its
own self-application guard.
-/
theorem fixedPointFree_forces_closed_self_guard
    {Alpha : Type u}
    {Beta : Type v}
    (E : GuardedEvaluator Alpha Beta)
    (step : Beta → Beta)
    (hfree : ∀ x, step x ≠ x)
    (a : Alpha)
    (hdiag : GuardedDiagonalWitness E step a) :
    ¬ E.allowed a a := by
  intro hopen
  rcases open_self_guard_forces_fixed_point E step a hdiag hopen with
    ⟨value, hfix⟩
  exact hfree value hfix

/--
If every code is allowed to self-apply, guarded diagonal representability
cannot coexist with a fixed-point-free step.
-/
theorem total_self_guard_incompatible_with_fixedPointFree
    {Alpha : Type u}
    {Beta : Type v}
    (E : GuardedEvaluator Alpha Beta)
    (step : Beta → Beta)
    (hfree : ∀ x, step x ≠ x)
    (htotal : ∀ a, E.allowed a a) :
    ¬ GuardedDiagonalRepresentable E step := by
  rintro ⟨a, hdiag⟩
  exact fixedPointFree_forces_closed_self_guard
    E step hfree a hdiag (htotal a)

/--
A completely closed guard demonstrates that guarded diagonal representation
alone does not force a fixed point.
-/
def closedEvaluator
    {Alpha : Type u}
    {Beta : Type v}
    (fallback : Beta) :
    GuardedEvaluator Alpha Beta where
  allowed := fun _ _ => False
  value := fun _ _ => fallback

theorem closedEvaluator_represents_every_diagonal
    {Alpha : Type u}
    {Beta : Type v}
    [Nonempty Alpha]
    (fallback : Beta)
    (step : Beta → Beta) :
    GuardedDiagonalRepresentable
      (closedEvaluator (Alpha := Alpha) fallback) step := by
  let a : Alpha := Classical.choice inferInstance
  refine ⟨a, ?_⟩
  intro x
  constructor
  · simp [closedEvaluator]
  · intro h
    exact False.elim h

/--
Concrete two-state consequence: any guarded representation of the crossing
diagonal must block self-application at its representing code.
-/
theorem twoState_guarded_diagonal_requires_closed_self_guard
    {Alpha : Type u}
    (E : GuardedEvaluator Alpha TwoState.Side)
    (a : Alpha)
    (hdiag : GuardedDiagonalWitness E TwoState.cross a) :
    ¬ E.allowed a a := by
  exact fixedPointFree_forces_closed_self_guard
    E TwoState.cross TwoState.cross_ne_self a hdiag

end GuardedLawvere
end DistinctionSelfReference
