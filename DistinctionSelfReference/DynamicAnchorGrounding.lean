import DistinctionSelfReference.LocalSufficiency
import DistinctionSelfReference.SchedulingCriterion

namespace DistinctionSelfReference
namespace DynamicAnchorGrounding

open LocalSufficiency
open LongRunRSI
open VariableDelayReality
open SchedulingCriterion

universe u v

/--
A schedule preserves stable grounded Boolean judgments when every Boolean
commitment that factors through a sufficient anchor can still be reconstructed
from the scheduled (possibly delayed/reordered) anchor observations and
converges to the same eventual target.
-/
def PreservesStableGroundedBool (S : Schedule) : Prop :=
  ∀ {World : Type u} {Anchor : Type v}
    (anchor : World → Anchor)
    (required : World → Bool)
    (trajectory : Nat → World)
    (target : Bool),
    Sufficient anchor required →
    EventuallyConstant (fun n => required (trajectory n)) target →
    ∃ post : Anchor → Bool,
      required = post ∘ anchor ∧
      EventuallyConstant
        (fun n => post (anchor (trajectory (S.source n)))) target

/--
Eventual freshness is sufficient for preservation of every eventually stable
goal-relevant Boolean judgment that is grounded through a sufficient anchor.
-/
theorem preservesStableGroundedBool_of_eventuallyFresh
    (S : Schedule)
    (hfresh : S.EventuallyFresh) :
    PreservesStableGroundedBool S := by
  intro World Anchor anchor required trajectory target hsufficient hstable
  rcases hsufficient with ⟨post, hfactor⟩
  refine ⟨post, hfactor, ?_⟩
  have hsampled :
      EventuallyConstant
        (fun n => required (trajectory (S.source n))) target :=
    retained_converges_of_eventuallyFresh
      S hfresh
      (required := fun n => required (trajectory n))
      (retained := fun n => required (trajectory (S.source n)))
      (target := target)
      (by intro n; rfl)
      hstable
  simpa [hfactor, Function.comp_apply] using hsampled

/--
Necessity: if every stable grounded Boolean judgment survives scheduled anchor
sampling, then the schedule must eventually leave every finite stale prefix.
The identity anchor on Nat is already enough to witness failure.
-/
theorem eventuallyFresh_of_preservesStableGroundedBool
    (S : Schedule)
    (hpres : PreservesStableGroundedBool S) :
    S.EventuallyFresh := by
  apply eventuallyFresh_of_preservesStableBool
  intro required target hstable
  have hsufficient :
      Sufficient (fun n : Nat => n) required :=
    ⟨required, by funext n; rfl⟩
  have hstable' :
      EventuallyConstant
        (fun n => required ((fun k : Nat => k) n)) target := by
    simpa using hstable
  rcases hpres
      (World := Nat)
      (Anchor := Nat)
      (anchor := fun n : Nat => n)
      (required := required)
      (trajectory := fun n : Nat => n)
      target
      hsufficient
      hstable' with
    ⟨post, hfactor, hdelayed⟩
  have hpost : required = post := by
    simpa [Function.comp_def] using hfactor
  simpa [hpost] using hdelayed

/--
Exact delayed-grounding criterion:
eventual freshness is equivalent to preserving all eventually stable Boolean
judgments grounded through sufficient anchors.
-/
theorem eventuallyFresh_iff_preservesStableGroundedBool
    (S : Schedule) :
    S.EventuallyFresh ↔ PreservesStableGroundedBool S := by
  constructor
  · exact preservesStableGroundedBool_of_eventuallyFresh S
  · exact eventuallyFresh_of_preservesStableGroundedBool S

/--
Static anchor sufficiency alone is not enough under delayed access to reality.
If a schedule is not eventually fresh, there is a Boolean goal process with a
fully sufficient identity anchor whose delayed observations fail to converge
to the true stable target.
-/
theorem sufficient_anchor_counterexample_of_not_eventuallyFresh
    (S : Schedule)
    (hnot : ¬ S.EventuallyFresh) :
    ∃ required : Nat → Bool, ∃ target : Bool,
      Sufficient (fun n : Nat => n) required ∧
      EventuallyConstant required target ∧
      ¬ EventuallyConstant (fun n => required (S.source n)) target := by
  rcases counterexample_of_not_eventuallyFresh S hnot with
    ⟨required, target, hstable, hfail⟩
  exact ⟨required, target, ⟨required, by funext n; rfl⟩, hstable, hfail⟩

/--
Bounded staleness is therefore a concrete sufficient condition for preserving
every stable grounded Boolean judgment.
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
