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
  have hsum : (∑ _x : α, (1 : ZMod 2)) = 0 :=
    Finset.sum_ninvolution (s := Finset.univ)
      (f := fun _ : α => (1 : ZMod 2)) D.cross
      (fun _ =>
        (ZMod.natCast_self 2 : (2 : ZMod 2) = 0))
      (fun x _ => by
        simpa [IsBoundary] using hfree x)
      (fun _ => by simp)
      D.involutive
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using hsum

/--
On a finite carrier of odd cardinality, an involutive distinction must have
a boundary/static fixed point.
-/
theorem existsBoundary_of_odd_fintype_card
    {α : Type u} [Fintype α]
    (D : InvolutiveDistinction α)
    (hodd : Odd (Fintype.card α)) :
    ∃ x, D.IsBoundary x := by
  by_contra hnone
  have hfree : ∀ x, ¬ D.IsBoundary x := by
    intro x hx
    exact hnone ⟨x, hx⟩
  exact (Nat.not_even_iff_odd.mpr hodd)
    (D.even_fintype_card_of_noBoundary hfree)

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
