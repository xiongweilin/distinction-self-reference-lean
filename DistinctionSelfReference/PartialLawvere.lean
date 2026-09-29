import DistinctionSelfReference.WeakRepresentation

namespace DistinctionSelfReference
namespace PartialLawvere

universe u v

/--
Partial diagonal representation: the code a represents the mapped diagonal
where undefined self-evaluations remain undefined.
-/
def PartialDiagonalWitness
    {Alpha : Type u}
    {Beta : Type v}
    (eval : Alpha → Alpha → Option Beta)
    (step : Beta → Beta)
    (a : Alpha) : Prop :=
  ∀ x, eval a x = Option.map step (eval x x)

def PartialDiagonalRepresentable
    {Alpha : Type u}
    {Beta : Type v}
    (eval : Alpha → Alpha → Option Beta)
    (step : Beta → Beta) : Prop :=
  ∃ a, PartialDiagonalWitness eval step a

/--
Exact partiality threshold: diagonal representation plus defined self-evaluation
forces an ordinary fixed point.
-/
theorem defined_partial_diagonal_forces_fixed_point
    {Alpha : Type u}
    {Beta : Type v}
    (eval : Alpha → Alpha → Option Beta)
    (step : Beta → Beta)
    (a : Alpha)
    (hdiag : PartialDiagonalWitness eval step a)
    (value : Beta)
    (hdefined : eval a a = some value) :
    step value = value := by
  have h := hdiag a
  rw [hdefined] at h
  simp at h
  exact h.symm

/--
For a fixed-point-free endomap, every partial diagonal witness must be guarded
by undefined self-application.
-/
theorem fixedPointFree_forces_undefined_selfApplication
    {Alpha : Type u}
    {Beta : Type v}
    (eval : Alpha → Alpha → Option Beta)
    (step : Beta → Beta)
    (hfree : ∀ x, step x ≠ x)
    (a : Alpha)
    (hdiag : PartialDiagonalWitness eval step a) :
    eval a a = none := by
  cases hself : eval a a with
  | none =>
      exact hself
  | some value =>
      exfalso
      have hfix :=
        defined_partial_diagonal_forces_fixed_point
          eval step a hdiag value hself
      exact hfree value hfix

/--
Hence partial diagonal representability is compatible with a fixed-point-free
step only by making every representing code undefined on its own code.
-/
theorem fixedPointFree_guarding_condition
    {Alpha : Type u}
    {Beta : Type v}
    (eval : Alpha → Alpha → Option Beta)
    (step : Beta → Beta)
    (hfree : ∀ x, step x ≠ x)
    (hrep : PartialDiagonalRepresentable eval step) :
    ∃ a,
      PartialDiagonalWitness eval step a ∧
      eval a a = none := by
  rcases hrep with ⟨a, ha⟩
  exact ⟨a, ha,
    fixedPointFree_forces_undefined_selfApplication
      eval step hfree a ha⟩

/--
A totally undefined evaluator witnesses that partial diagonal representation
alone does not force a fixed point.
-/
def nowhereEval
    {Alpha : Type u}
    {Beta : Type v} :
    Alpha → Alpha → Option Beta :=
  fun _ _ => none

theorem nowhereEval_represents_every_partial_diagonal
    {Alpha : Type u}
    {Beta : Type v}
    [Nonempty Alpha]
    (step : Beta → Beta) :
    PartialDiagonalRepresentable
      (nowhereEval : Alpha → Alpha → Option Beta) step := by
  let a : Alpha := Classical.choice inferInstance
  refine ⟨a, ?_⟩
  intro x
  rfl

theorem twoState_partial_diagonal_requires_guard
    {Alpha : Type u}
    (eval : Alpha → Alpha → Option TwoState.Side)
    (a : Alpha)
    (hdiag : PartialDiagonalWitness eval TwoState.cross a) :
    eval a a = none := by
  exact fixedPointFree_forces_undefined_selfApplication
    eval TwoState.cross TwoState.cross_ne_self a hdiag

end PartialLawvere
end DistinctionSelfReference
