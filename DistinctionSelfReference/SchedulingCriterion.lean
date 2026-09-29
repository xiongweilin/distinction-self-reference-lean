import DistinctionSelfReference.VariableDelayReality

namespace DistinctionSelfReference
namespace SchedulingCriterion

open LongRunRSI
open VariableDelayReality

/--
A schedule preserves every eventually stable Boolean requirement when sampling
the requirement through its source indices preserves the same eventual target.
Boolean requirements already suffice to test freshness exactly.
-/
def PreservesStableBool
    (S : Schedule) : Prop :=
  ∀ (required : Nat → Bool) (target : Bool),
    EventuallyConstant required target →
    EventuallyConstant (fun n => required (S.source n)) target

theorem preservesStableBool_of_eventuallyFresh
    (S : Schedule)
    (hfresh : S.EventuallyFresh) :
    PreservesStableBool S := by
  intro required target hreq
  exact retained_converges_of_eventuallyFresh
    S hfresh (required := required)
    (retained := fun n => required (S.source n))
    (target := target) (by intro n; rfl) hreq

/--
Necessity: if a schedule preserves every eventually stable Boolean requirement,
it must eventually leave every finite stale prefix behind.
-/
theorem eventuallyFresh_of_preservesStableBool
    (S : Schedule)
    (hpres : PreservesStableBool S) :
    S.EventuallyFresh := by
  intro cutoff
  let required : Nat → Bool := fun k => decide (cutoff ≤ k)
  have hreq : EventuallyConstant required true := by
    refine ⟨cutoff, ?_⟩
    intro k hk
    simp [required, hk]
  rcases hpres required true hreq with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have htrue := hN n hn
  change decide (cutoff ≤ S.source n) = true at htrue
  exact of_decide_eq_true htrue

/--
Exact criterion: eventual freshness is equivalent to preservation of all
eventually stable Boolean reality requirements.
-/
theorem eventuallyFresh_iff_preservesStableBool
    (S : Schedule) :
    S.EventuallyFresh ↔ PreservesStableBool S := by
  constructor
  · exact preservesStableBool_of_eventuallyFresh S
  · exact eventuallyFresh_of_preservesStableBool S

/--
Failure of eventual freshness therefore always admits a Boolean stable-reality
counterexample, not only the permanently-stale special case.
-/
theorem counterexample_of_not_eventuallyFresh
    (S : Schedule)
    (hnot : ¬ S.EventuallyFresh) :
    ∃ required : Nat → Bool, ∃ target : Bool,
      EventuallyConstant required target ∧
      ¬ EventuallyConstant (fun n => required (S.source n)) target := by
  by_contra h
  push Not at h
  have hpres : PreservesStableBool S := by
    intro required target hreq
    exact h required target hreq
  exact hnot (eventuallyFresh_of_preservesStableBool S hpres)

end SchedulingCriterion
end DistinctionSelfReference
