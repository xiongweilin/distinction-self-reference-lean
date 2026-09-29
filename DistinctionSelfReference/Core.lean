import Mathlib.Dynamics.FixedPoints.Basic

namespace DistinctionSelfReference

universe u

/--
A minimal candidate structure for a crossing distinction.

It deliberately captures only the crossing condition: crossing twice returns
to the starting state. It does not claim to formalize the whole calculus of
indications.
-/
structure InvolutiveDistinction (α : Type u) where
  cross : α → α
  involutive : Function.Involutive cross

namespace InvolutiveDistinction

variable {α : Type u}

/-- A state is a boundary/self-dual state when crossing leaves it unchanged. -/
def IsBoundary (D : InvolutiveDistinction α) (x : α) : Prop :=
  D.cross x = x

/-- A nontrivial re-entry orbit has two distinct states and returns after two crossings. -/
def IsTwoCycle (D : InvolutiveDistinction α) (x : α) : Prop :=
  D.cross x ≠ x ∧ D.cross (D.cross x) = x

/-- Every state returns after two crossings. -/
theorem returnsAfterTwo (D : InvolutiveDistinction α) (x : α) :
    D.cross (D.cross x) = x :=
  D.involutive x

/-- Static self-reference for a crossing system is exactly being a boundary state. -/
theorem isBoundary_iff_fixedPoint (D : InvolutiveDistinction α) (x : α) :
    D.IsBoundary x ↔ Function.IsFixedPt D.cross x :=
  Iff.rfl

/--
Every state of an involutive distinction is either a static fixed point or
belongs to a nontrivial two-cycle. No longer orbit can occur.
-/
theorem boundary_or_twoCycle (D : InvolutiveDistinction α) (x : α) :
    D.IsBoundary x ∨ D.IsTwoCycle x := by
  by_cases h : D.cross x = x
  · exact Or.inl h
  · exact Or.inr ⟨h, D.involutive x⟩

/-- A two-cycle state cannot simultaneously be a boundary state. -/
theorem twoCycle_not_boundary (D : InvolutiveDistinction α) (x : α)
    (h : D.IsTwoCycle x) : ¬ D.IsBoundary x :=
  h.1

end InvolutiveDistinction

/--
A generic re-entry system. Unlike InvolutiveDistinction, the update need not
be involutive. This is the weak interface used to compare static and dynamic
notions of self-reference.
-/
structure ReentrySystem (α : Type u) where
  step : α → α

namespace ReentrySystem

variable {α : Type u}

def IsStaticSelfReference (S : ReentrySystem α) (x : α) : Prop :=
  Function.IsFixedPt S.step x

def ReturnsAfter (S : ReentrySystem α) (n : ℕ) (x : α) : Prop :=
  (S.step^[n]) x = x

end ReentrySystem

end DistinctionSelfReference
