import DistinctionSelfReference.LocalSufficiency
import DistinctionSelfReference.SchedulingCriterion

namespace DistinctionSelfReference
namespace DynamicAnchorGrounding

open LocalSufficiency
open InformationOrder
open LongRunRSI
open VariableDelayReality
open SchedulingCriterion

/--
A schedule preserves stable grounded Boolean judgments when every eventually
stable Boolean commitment that factors through a finite Boolean anchor can
still be reconstructed from the scheduled (possibly delayed/reordered) anchor
observations and converges to the same target.
-/
def PreservesStableGroundedBool (S : Schedule) : Prop :=
  ∀ (anchor : Nat → Bool)
    (required : Nat → Bool)
    (target : Bool),
    Sufficient anchor required →
    EventuallyConstant required target →
    ∃ post : Bool → Bool,
      required = post ∘ anchor ∧
      EventuallyConstant
        (fun n => post (anchor (S.source n))) target

/--
Eventual freshness is sufficient for preservation of every eventually stable
Boolean judgment grounded through a sufficient finite Boolean anchor.
-/
theorem preservesStableGroundedBool_of_eventuallyFresh
    (S : Schedule)
    (hfresh : S.EventuallyFresh) :
    PreservesStableGroundedBool S := by
  intro anchor required target hsufficient hstable
  rcases hsufficient with ⟨post, hfactor⟩
  refine ⟨post, hfactor, ?_⟩
  have hsampled :
      EventuallyConstant
        (fun n => required (S.source n)) target :=
    retained_converges_of_eventuallyFresh
      S hfresh
      (required := required)
      (retained := fun n => required (S.source n))
      (target := target)
      (by intro n; rfl)
      hstable
  simpa [hfactor, Function.comp_apply] using hsampled

/--
Necessity already holds for a two-valued anchor: if every stable judgment
grounded through a sufficient Bool anchor survives scheduled sampling, the
schedule must eventually leave every finite stale prefix behind.
-/
theorem eventuallyFresh_of_preservesStableGroundedBool
    (S : Schedule)
    (hpres : PreservesStableGroundedBool S) :
    S.EventuallyFresh := by
  apply eventuallyFresh_of_preservesStableBool
  intro required target hstable
  have hsufficient : Sufficient required required :=
    refines_refl required
  rcases hpres required required target hsufficient hstable with
    ⟨post, hfactor, hdelayed⟩
  have hpoint : ∀ k, post (required k) = required k := by
    intro k
    exact (congrFun hfactor k).symm
  rcases hdelayed with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  change required (S.source n) = target
  calc
    required (S.source n) = post (required (S.source n)) :=
      (hpoint (S.source n)).symm
    _ = target := hN n hn

/--
Exact delayed-grounding criterion:
eventual freshness is equivalent to preserving all eventually stable Boolean
judgments grounded through sufficient finite Boolean anchors.
-/
theorem eventuallyFresh_iff_preservesStableGroundedBool
    (S : Schedule) :
    S.EventuallyFresh ↔ PreservesStableGroundedBool S := by
  constructor
  · exact preservesStableGroundedBool_of_eventuallyFresh S
  · exact eventuallyFresh_of_preservesStableGroundedBool S

/--
Static anchor sufficiency alone is not enough under delayed access to reality.
If a schedule is not eventually fresh, there is an eventually stable Boolean
goal process whose own two-valued judgment is a sufficient finite anchor, yet
the delayed observations fail to converge to the true target.
-/
theorem sufficient_bool_anchor_counterexample_of_not_eventuallyFresh
    (S : Schedule)
    (hnot : ¬ S.EventuallyFresh) :
    ∃ required : Nat → Bool, ∃ target : Bool,
      Sufficient required required ∧
      EventuallyConstant required target ∧
      ¬ EventuallyConstant (fun n => required (S.source n)) target := by
  rcases counterexample_of_not_eventuallyFresh S hnot with
    ⟨required, target, hstable, hfail⟩
  exact ⟨required, target, refines_refl required, hstable, hfail⟩

/--
Bounded staleness is therefore a concrete sufficient condition for preserving
every stable judgment grounded through a finite Boolean anchor.
-/
theorem preservesStableGroundedBool_of_boundedStaleness
    (S : Schedule)
    (lag : Nat)
    (hbound : S.BoundedStaleness lag) :
    PreservesStableGroundedBool S :=
  preservesStableGroundedBool_of_eventuallyFresh S
    (S.eventuallyFresh_of_boundedStaleness lag hbound)

end DynamicAnchorGrounding
end DistinctionSelfReference
