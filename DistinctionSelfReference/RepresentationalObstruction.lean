import DistinctionSelfReference.Representational
import DistinctionSelfReference.TwoState

namespace DistinctionSelfReference
namespace RepresentationalObstruction

universe u v

/--
A fixed-point-free endomap on the represented result type is incompatible
with a Lawvere-style surjective evaluator.
-/
theorem fixedPointFree_forbids_surjective_representation
    {Alpha : Type u} {Beta : Type v}
    (step : Beta → Beta)
    (hfree : ∀ x, step x ≠ x) :
    ¬ ∃ eval : Alpha → Alpha → Beta, Function.Surjective eval := by
  rintro ⟨eval, heval⟩
  rcases Representational.surjective_representation_forces_fixed_point
      eval heval step with ⟨x, hx⟩
  exact hfree x hx

/--
The minimal two-state crossing therefore cannot be the result type of a
universal point-surjective self-representation.
-/
theorem twoState_forbids_surjective_representation
    {Alpha : Type u} :
    ¬ ∃ eval : Alpha → Alpha → TwoState.Side, Function.Surjective eval :=
  fixedPointFree_forbids_surjective_representation
    TwoState.cross TwoState.cross_ne_self

/--
More generally, surjective representation rules out every fixed-point-free
endomap on the represented result type.
-/
theorem surjective_representation_forbids_fixedPointFree
    {Alpha : Type u} {Beta : Type v}
    (eval : Alpha → Alpha → Beta)
    (heval : Function.Surjective eval) :
    ¬ ∃ step : Beta → Beta, ∀ x, step x ≠ x := by
  rintro ⟨step, hfree⟩
  rcases Representational.surjective_representation_forces_fixed_point
      eval heval step with ⟨x, hx⟩
  exact hfree x hx

end RepresentationalObstruction
end DistinctionSelfReference
