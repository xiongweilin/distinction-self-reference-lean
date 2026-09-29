import Mathlib.Order.FixedPoints

namespace DistinctionSelfReference
namespace LabeledBisimulation

universe u v

/--
A labelled transition system with a proposition-valued observation.
Using a proposition avoids imposing decidability on observations.
-/
structure System (Label : Type u) (State : Type v) where
  step : State → Label → State → Prop
  observe : State → Prop

namespace System

variable {Label : Type u} {State : Type v}

abbrev Rel (State : Type v) := Set (State × State)

/-- One-step labelled bisimulation transformer. -/
def transfer (T : System Label State) (R : Rel State) : Rel State :=
  { p |
      (T.observe p.1 ↔ T.observe p.2) ∧
      (∀ a s', T.step p.1 a s' →
        ∃ t', T.step p.2 a t' ∧ (s', t') ∈ R) ∧
      (∀ a t', T.step p.2 a t' →
        ∃ s', T.step p.1 a s' ∧ (s', t') ∈ R) }

theorem transfer_mono (T : System Label State) :
    Monotone T.transfer := by
  intro R Q hRQ p hp
  rcases hp with ⟨hobs, hforth, hback⟩
  refine ⟨hobs, ?_, ?_⟩
  · intro a s' hs'
    rcases hforth a s' hs' with ⟨t', ht', hrel⟩
    exact ⟨t', ht', hRQ hrel⟩
  · intro a t' ht'
    rcases hback a t' ht' with ⟨s', hs', hrel⟩
    exact ⟨s', hs', hRQ hrel⟩

def operator (T : System Label State) : Rel State →o Rel State where
  toFun := T.transfer
  monotone' := T.transfer_mono

/-- Label-preserving bisimilarity is the greatest fixed point. -/
def Bisimilar (T : System Label State) (s t : State) : Prop :=
  (s, t) ∈ T.operator.gfp

theorem bisimilar_unfold (T : System Label State) (s t : State) :
    T.Bisimilar s t ↔ (s, t) ∈ T.transfer T.operator.gfp := by
  change (s, t) ∈ T.operator.gfp ↔ (s, t) ∈ T.operator T.operator.gfp
  rw [T.operator.isFixedPt_gfp]

theorem bisimilar_observe
    (T : System Label State) {s t : State}
    (h : T.Bisimilar s t) :
    T.observe s ↔ T.observe t :=
  (T.bisimilar_unfold s t).mp h |>.1

theorem bisimilar_match_forward
    (T : System Label State) {s t s' : State}
    (a : Label)
    (h : T.Bisimilar s t)
    (hs : T.step s a s') :
    ∃ t', T.step t a t' ∧ T.Bisimilar s' t' :=
  (T.bisimilar_unfold s t).mp h |>.2.1 a s' hs

/-- Coinduction for labelled bisimilarity. -/
theorem subset_bisimilar_of_postfixed
    (T : System Label State) (R : Rel State)
    (hR : R ⊆ T.transfer R) :
    R ⊆ T.operator.gfp :=
  T.operator.le_gfp hR

/-- Every state is bisimilar to itself. -/
theorem bisimilar_refl (T : System Label State) (s : State) :
    T.Bisimilar s s := by
  let R : Rel State := { p | p.1 = p.2 }
  have hpost : R ⊆ T.transfer R := by
    intro p hp
    rcases p with ⟨x, y⟩
    change x = y at hp
    subst y
    refine ⟨Iff.rfl, ?_, ?_⟩
    · intro a x' hx'
      exact ⟨x', hx', rfl⟩
    · intro a x' hx'
      exact ⟨x', hx', rfl⟩
  exact T.subset_bisimilar_of_postfixed R hpost (by rfl)

end System
end LabeledBisimulation
end DistinctionSelfReference
