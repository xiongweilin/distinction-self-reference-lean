import DistinctionSelfReference.NextRSIDependencyGraph
import DistinctionSelfReference.FullVersionDiagnostics

namespace DistinctionSelfReference
namespace NextRSIConflict

open MetaFramework
open NextRSIDependencyGraph
open CapabilityOrder
open SelfModification

/-- Realizations range over arbitrary Bool-capability full-version modifiers. -/
structure CycleRealization where
  modifier : Modifier (CapVersion Bool Bool)
  start : CapVersion Bool Bool

/--
Only the three cycle/growth conditions receive structural meanings here;
other next-phase conditions are irrelevant to this incompatibility witness.
-/
def semantics : ConditionSemantics Condition where
  Realization := CycleRealization
  holds r c :=
    match c with
    | .pointwiseNonDegradation =>
        ∀ x, x.profile ≤ (r.modifier.propose x).profile
    | .fullVersionRecurrence =>
        FullVersionDiagnostics.Recurrent r.modifier r.start
    | .strictFirstCapabilityGrowth =>
        CapabilityDynamics.StrictGrowth
          r.start.profile (r.modifier.propose r.start).profile
    | _ => True

/--
A non-degrading recurrent full-version process cannot strictly improve its
capability profile on the first step: recurrence would force the whole cycle
to be a capability plateau.
-/
theorem recurrence_strictGrowth_incompatible :
    semantics.Incompatible
      { Condition.pointwiseNonDegradation,
        Condition.fullVersionRecurrence,
        Condition.strictFirstCapabilityGrowth } := by
  rintro ⟨r, hr⟩
  have hnon : ∀ x, x.profile ≤ (r.modifier.propose x).profile :=
    hr (c := Condition.pointwiseNonDegradation) (by simp)
  have hrec : FullVersionDiagnostics.Recurrent r.modifier r.start :=
    hr (c := Condition.fullVersionRecurrence) (by simp)
  have hstrict : CapabilityDynamics.StrictGrowth
      r.start.profile (r.modifier.propose r.start).profile :=
    hr (c := Condition.strictFirstCapabilityGrowth) (by simp)
  rcases hrec with ⟨k, hk, hcycle⟩
  have hfirst : 0 + 1 ≤ k := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hk)
  have hno := FullVersionDiagnostics.no_strict_growth_inside_recurrence
    r.modifier r.start hnon hcycle hfirst
  apply hno
  simpa using hstrict

end NextRSIConflict
end DistinctionSelfReference
