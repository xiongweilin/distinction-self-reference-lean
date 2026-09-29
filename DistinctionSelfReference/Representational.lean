import Mathlib.Logic.Function.Basic

namespace DistinctionSelfReference
namespace Representational

universe u v

/--
A type-level Lawvere bridge already available in Mathlib.

If states in α can represent every observation α → β through a single
surjective evaluator, then every endomap on β has a fixed point.
-/
theorem surjective_representation_forces_fixed_point
    {α : Type u} {β : Type v}
    (eval : α → α → β)
    (surjective : Function.Surjective eval)
    (step : β → β) :
    ∃ x, step x = x :=
  Function.exists_fixed_point_of_surjective eval surjective step

end Representational
end DistinctionSelfReference
