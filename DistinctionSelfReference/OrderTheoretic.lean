import Mathlib.Order.FixedPoints
import DistinctionSelfReference.Core

namespace DistinctionSelfReference
namespace OrderTheoretic

universe u

/--
Knaster-Tarski bridge: complete-lattice structure plus monotonicity is sufficient
to force a static fixed point.
-/
theorem monotone_has_static_self_reference
    {α : Type u} [CompleteLattice α] (f : α →o α) :
    ∃ x, Function.IsFixedPt f x :=
  ⟨f.lfp, f.isFixedPt_lfp⟩

/-- The fixed point furnished by lfp is least among all fixed points. -/
theorem least_static_self_reference
    {α : Type u} [CompleteLattice α] (f : α →o α) :
    Function.IsFixedPt f f.lfp ∧
      ∀ x, Function.IsFixedPt f x → f.lfp ≤ x := by
  constructor
  · exact f.isFixedPt_lfp
  · intro x hx
    exact f.lfp_le_fixed hx

/-- Dually, gfp is the greatest fixed point. -/
theorem greatest_static_self_reference
    {α : Type u} [CompleteLattice α] (f : α →o α) :
    Function.IsFixedPt f f.gfp ∧
      ∀ x, Function.IsFixedPt f x → x ≤ f.gfp := by
  constructor
  · exact f.isFixedPt_gfp
  · intro x hx
    exact f.fixed_le_gfp hx

end OrderTheoretic
end DistinctionSelfReference
