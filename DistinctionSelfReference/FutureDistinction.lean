import Mathlib.Computability.MyhillNerode

namespace DistinctionSelfReference
namespace FutureDistinction

universe u

/--
Two histories are future-indistinguishable for a language when every possible
continuation gives the same acceptance answer.
-/
def FutureEq {α : Type u} (L : Language α) (x y : List α) : Prop :=
  L.leftQuotient x = L.leftQuotient y

theorem futureEq_iff_same_continuations
    {α : Type u} (L : Language α) (x y : List α) :
    FutureEq L x y ↔
      ∀ z : List α, (x ++ z ∈ L ↔ y ++ z ∈ L) := by
  constructor
  · intro h z
    change z ∈ L.leftQuotient x ↔ z ∈ L.leftQuotient y
    rw [h]
  · intro h
    ext z
    change x ++ z ∈ L ↔ y ++ z ∈ L
    exact h z

theorem futureEq_refl
    {α : Type u} (L : Language α) (x : List α) :
    FutureEq L x x :=
  rfl

theorem futureEq_symm
    {α : Type u} {L : Language α} {x y : List α}
    (h : FutureEq L x y) :
    FutureEq L y x :=
  h.symm

theorem futureEq_trans
    {α : Type u} {L : Language α} {x y z : List α}
    (hxy : FutureEq L x y) (hyz : FutureEq L y z) :
    FutureEq L x z :=
  hxy.trans hyz

/-- The canonical state representation of a history is its future behavior. -/
def stateOf {α : Type u} (L : Language α) (x : List α) :
    Set.range L.leftQuotient :=
  ⟨L.leftQuotient x, ⟨x, rfl⟩⟩

theorem stateOf_eq_iff_futureEq
    {α : Type u} (L : Language α) (x y : List α) :
    stateOf L x = stateOf L y ↔ FutureEq L x y := by
  constructor
  · intro h
    exact Subtype.ext_iff.mp h
  · intro h
    exact Subtype.ext h

/--
Myhill-Nerode bridge: finite future-distinction state space is exactly regularity.
-/
theorem regular_iff_finite_future_states
    {α : Type u} (L : Language α) :
    L.IsRegular ↔ (Set.range L.leftQuotient).Finite :=
  Language.isRegular_iff_finite_range_leftQuotient

end FutureDistinction
end DistinctionSelfReference
