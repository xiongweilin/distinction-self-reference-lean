import DistinctionSelfReference.FutureDistinction
import DistinctionSelfReference.LabeledBisimulation

namespace DistinctionSelfReference
namespace FutureBisimulation

universe u

open FutureDistinction

/-- The canonical residual DFA viewed as a labelled observed transition system. -/
def canonicalSystem {α : Type u} (L : Language α) :
    LabeledBisimulation.System α (Set.range L.leftQuotient) where
  step s a t := L.toDFA.step s a = t
  observe s := s ∈ L.toDFA.accept

abbrev ResidualRel {α : Type u} (L : Language α) :=
  Set (Set.range L.leftQuotient × Set.range L.leftQuotient)

/-- Equality of residual languages is preserved by one labelled transition step. -/
theorem sameFuture_postfixed
    {α : Type u} (L : Language α) :
    { p : Set.range L.leftQuotient × Set.range L.leftQuotient |
        p.1.val = p.2.val } ⊆
      (canonicalSystem L).transfer
        { p : Set.range L.leftQuotient × Set.range L.leftQuotient |
          p.1.val = p.2.val } := by
  intro p hp
  rcases p with ⟨s, t⟩
  change s.val = t.val at hp
  refine ⟨?_, ?_, ?_⟩
  · change s ∈ L.toDFA.accept ↔ t ∈ L.toDFA.accept
    simpa only [Language.mem_accept_toDFA] using
      Set.mem_congr (congrArg (fun K : Language α => K) hp)
  · intro a s' hs'
    change L.toDFA.step s a = s' at hs'
    subst s'
    refine ⟨L.toDFA.step t a, rfl, ?_⟩
    change (L.toDFA.step s a).val = (L.toDFA.step t a).val
    simp only [Language.step_toDFA]
    rw [hp]
  · intro a t' ht'
    change L.toDFA.step t a = t' at ht'
    subst t'
    refine ⟨L.toDFA.step s a, rfl, ?_⟩
    change (L.toDFA.step s a).val = (L.toDFA.step t a).val
    simp only [Language.step_toDFA]
    rw [hp]

/-- Equal future behaviors are bisimilar in the canonical residual automaton. -/
theorem sameFuture_bisimilar
    {α : Type u} (L : Language α)
    {s t : Set.range L.leftQuotient}
    (h : s.val = t.val) :
    (canonicalSystem L).Bisimilar s t := by
  apply (canonicalSystem L).subset_bisimilar_of_postfixed
    { p : Set.range L.leftQuotient × Set.range L.leftQuotient |
      p.1.val = p.2.val }
    (sameFuture_postfixed L)
  exact h

/-- Evaluation in the residual DFA computes successive left quotients. -/
theorem evalFrom_val
    {α : Type u} (L : Language α)
    (s : Set.range L.leftQuotient) (z : List α) :
    (L.toDFA.evalFrom s z).val = s.val.leftQuotient z := by
  induction z generalizing s with
  | nil =>
      rfl
  | cons a z ih =>
      rw [DFA.evalFrom_cons, ih]
      simp only [Language.step_toDFA]
      rw [← Language.leftQuotient_append]
      rfl

/-- Membership in a residual language is exactly acceptance from its DFA state. -/
theorem mem_val_iff_acceptsFrom
    {α : Type u} (L : Language α)
    (s : Set.range L.leftQuotient) (z : List α) :
    z ∈ s.val ↔ L.toDFA.evalFrom s z ∈ L.toDFA.accept := by
  rw [Language.mem_accept_toDFA]
  rw [evalFrom_val]
  simp

/-- Bisimilarity is preserved by reading the same continuation. -/
theorem bisimilar_evalFrom
    {α : Type u} (L : Language α)
    {s t : Set.range L.leftQuotient}
    (h : (canonicalSystem L).Bisimilar s t)
    (z : List α) :
    (canonicalSystem L).Bisimilar
      (L.toDFA.evalFrom s z) (L.toDFA.evalFrom t z) := by
  induction z generalizing s t with
  | nil =>
      simpa using h
  | cons a z ih =>
      simp only [DFA.evalFrom_cons]
      apply ih
      rcases (canonicalSystem L).bisimilar_match_forward a h rfl with
        ⟨t', ht', hnext⟩
      change L.toDFA.step t a = t' at ht'
      subst t'
      exact hnext

/-- Canonical residual states that are bisimilar have the same future language. -/
theorem bisimilar_sameFuture
    {α : Type u} (L : Language α)
    {s t : Set.range L.leftQuotient}
    (h : (canonicalSystem L).Bisimilar s t) :
    s.val = t.val := by
  ext z
  have hz := bisimilar_evalFrom L h z
  have hobs := (canonicalSystem L).bisimilar_observe hz
  change
    (L.toDFA.evalFrom s z ∈ L.toDFA.accept ↔
      L.toDFA.evalFrom t z ∈ L.toDFA.accept) at hobs
  constructor
  · intro hs
    apply (mem_val_iff_acceptsFrom L t z).mpr
    exact hobs.mp ((mem_val_iff_acceptsFrom L s z).mp hs)
  · intro ht
    apply (mem_val_iff_acceptsFrom L s z).mpr
    exact hobs.mpr ((mem_val_iff_acceptsFrom L t z).mp ht)

/--
On the canonical residual automaton, future indistinguishability of histories
is exactly labelled bisimilarity of their canonical states.
-/
theorem futureEq_iff_bisimilar
    {α : Type u} (L : Language α) (x y : List α) :
    FutureEq L x y ↔
      (canonicalSystem L).Bisimilar (stateOf L x) (stateOf L y) := by
  constructor
  · intro h
    apply sameFuture_bisimilar L
    exact h
  · intro h
    exact bisimilar_sameFuture L h

end FutureBisimulation
end DistinctionSelfReference
