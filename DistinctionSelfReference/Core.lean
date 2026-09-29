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

/-- A state is a boundary/self-dual state when crossing leaves it unchanged. -/
def IsBoundary (D : InvolutiveDistinction α) (x : α) : Prop :=
  D.cross x = x

/-- Every state returns after two crossings. -/
theorem returnsAfterTwo (D : InvolutiveDistinction α) (x : α) :
    D.cross (D.cross x) = x :=
  D.involutive x

/-- Static self-reference for a crossing system is exactly being a boundary state. -/
theorem isBoundary_iff_fixedPoint (D : InvolutiveDistinction α) (x : α) :
    D.IsBoundary x ↔ Function.IsFixedPt D.cross x :=
  Iff.rfl

end InvolutiveDistinction

/--
A generic re-entry system. Unlike InvolutiveDistinction, the update need not
be involutive. This is the weak interface used to compare static and dynamic
notions of self-reference.
-/
structure ReentrySystem (α : Type u) where
  step : α → α

namespace ReentrySystem

def IsStaticSelfReference (S : ReentrySystem α) (x : α) : Prop :=
  Function.IsFixedPt S.step x

def ReturnsAfter (S : ReentrySystem α) (n : ℕ) (x : α) : Prop :=
  (S.step^[n]) x = x

end ReentrySystem

end DistinctionSelfReference
