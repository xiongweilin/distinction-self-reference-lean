import Mathlib.Order.FixedPoints

namespace DistinctionSelfReference
namespace Bisimulation

universe u v

/--
An observed transition system. Identity across change is not primitive here:
it will be represented by the greatest relation that preserves observation and
can match transitions in both directions.
-/
structure System (State : Type u) (Obs : Type v) where
  step : State → State → Prop
  observe : State → Obs

namespace System

variable {State : Type u} {Obs : Type v}

abbrev Rel (State : Type u) := Set (State × State)

/--
One-step bisimulation transformer.
-/
def transfer (T : System State Obs) (R : Rel State) : Rel State :=
  { p |
      T.observe p.1 = T.observe p.2 ∧
      (∀ s', T.step p.1 s' → ∃ t', T.step p.2 t' ∧ (s', t') ∈ R) ∧
      (∀ t', T.step p.2 t' → ∃ s', T.step p.1 s' ∧ (s', t') ∈ R) }

theorem transfer_mono (T : System State Obs) :
    Monotone T.transfer := by
  intro R Q hRQ p hp
  rcases hp with ⟨hobs, hforth, hback⟩
  refine ⟨hobs, ?_, ?_⟩
  · intro s' hs'
    rcases hforth s' hs' with ⟨t', ht', hrel⟩
    exact ⟨t', ht', hRQ hrel⟩
  · intro t' ht'
    rcases hback t' ht' with ⟨s', hs', hrel⟩
    exact ⟨s', hs', hRQ hrel⟩

def operator (T : System State Obs) : Rel State →o Rel State where
  toFun := T.transfer
  monotone' := T.transfer_mono

/--
Bisimilarity is the greatest fixed point of the one-step transfer operator.
-/
def Bisimilar (T : System State Obs) (s t : State) : Prop :=
  (s, t) ∈ T.operator.gfp

theorem bisimilar_unfold (T : System State Obs) (s t : State) :
    T.Bisimilar s t ↔ (s, t) ∈ T.transfer T.operator.gfp := by
  change (s, t) ∈ T.operator.gfp ↔ (s, t) ∈ T.operator T.operator.gfp
  rw [T.operator.isFixedPt_gfp]

theorem bisimilar_observe
    (T : System State Obs) {s t : State}
    (h : T.Bisimilar s t) :
    T.observe s = T.observe t := by
  exact (T.bisimilar_unfold s t).mp h |>.1

theorem bisimilar_match_forward
    (T : System State Obs) {s t s' : State}
    (h : T.Bisimilar s t)
    (hs : T.step s s') :
    ∃ t', T.step t t' ∧ T.Bisimilar s' t' := by
  exact (T.bisimilar_unfold s t).mp h |>.2.1 s' hs

/--
Coinduction principle: any relation preserved by one transfer step is contained
in bisimilarity.
-/
theorem subset_bisimilar_of_postfixed
    (T : System State Obs) (R : Rel State)
    (hR : R ⊆ T.transfer R) :
    R ⊆ T.operator.gfp :=
  T.operator.le_gfp hR

end System
end Bisimulation
end DistinctionSelfReference
