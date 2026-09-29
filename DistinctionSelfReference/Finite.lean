import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import DistinctionSelfReference.Core

namespace DistinctionSelfReference
namespace InvolutiveDistinction

universe u

open scoped BigOperators

/--
A finite fixed-point-free involutive distinction has even cardinality.

The proof works modulo 2: give every state weight 1 and pair each state
with its crossing partner. Every pair contributes 1 + 1 = 0 in ZMod 2.
-/
theorem even_fintype_card_of_noBoundary
    {α : Type u} [Fintype α]
    (D : InvolutiveDistinction α)
    (hfree : ∀ x, ¬ D.IsBoundary x) :
    Even (Fintype.card α) := by
  rw [← ZMod.natCast_eq_zero_iff_even]
  have hsum : (∑ _x : α, (1 : ZMod 2)) = 0 := by
    apply Finset.sum_ninvolution (s := Finset.univ)
      (f := fun _ : α => (1 : ZMod 2)) D.cross
    · intro x
      norm_num
    · intro x _
      simpa [IsBoundary] using hfree x
    · intro x
      simp
    · intro x
      exact D.involutive x
  simpa using hsum

/--
Finite-type version stated with Nat.card, avoiding a chosen Fintype in the API.
-/
theorem even_natCard_of_noBoundary
    {α : Type u} [Finite α]
    (D : InvolutiveDistinction α)
    (hfree : ∀ x, ¬ D.IsBoundary x) :
    Even (Nat.card α) := by
  letI := Fintype.ofFinite α
  simpa [Nat.card_eq_fintype_card] using
    D.even_fintype_card_of_noBoundary hfree

end InvolutiveDistinction
end DistinctionSelfReference
