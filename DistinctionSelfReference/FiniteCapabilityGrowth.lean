import DistinctionSelfReference.CapabilityDynamics

namespace DistinctionSelfReference
namespace FiniteCapabilityGrowth

open CapabilityOrder
open CapabilityDynamics

universe u

variable {Capability : Type u}

/--
If the first n transitions of a capability chain are all strict, then the final
profile contains at least n capabilities.
-/
theorem steps_le_final_ncard
    [Finite Capability]
    (chain : Nat → Profile Capability)
    (n : Nat)
    (hstrict : ∀ k, k < n →
      StrictGrowth (chain k) (chain (k + 1))) :
    n ≤ (chain n).capabilities.ncard := by
  induction n with
  | zero =>
      exact Nat.zero_le _
  | succ n ih =>
      have hprefix : ∀ k, k < n →
          StrictGrowth (chain k) (chain (k + 1)) := by
        intro k hk
        exact hstrict k (lt_trans hk (Nat.lt_succ_self n))
      have hn : n ≤ (chain n).capabilities.ncard :=
        ih hprefix
      have hgrow :
          (chain n).capabilities.ncard <
            (chain (n + 1)).capabilities.ncard :=
        ncard_lt_of_strictGrowth
          (hstrict n (Nat.lt_succ_self n))
      exact Nat.succ_le_of_lt (lt_of_le_of_lt hn hgrow)

/--
Global finite-universe bound: there cannot be more consecutive strict
capability-growth transitions than the total number of possible capabilities.
-/
theorem strictGrowth_steps_le_total
    [Finite Capability]
    (chain : Nat → Profile Capability)
    (n : Nat)
    (hstrict : ∀ k, k < n →
      StrictGrowth (chain k) (chain (k + 1))) :
    n ≤ Nat.card Capability := by
  exact le_trans
    (steps_le_final_ncard chain n hstrict)
    (ncard_le_total (chain n))

/--
Therefore an attempted prefix longer than the finite capability universe must
contain at least one non-strict step.
-/
theorem exists_nonStrict_before_succ_total
    [Finite Capability]
    (chain : Nat → Profile Capability) :
    ∃ k, k < Nat.card Capability + 1 ∧
      ¬ StrictGrowth (chain k) (chain (k + 1)) := by
  by_contra h
  push_neg at h
  have hbound :=
    strictGrowth_steps_le_total chain (Nat.card Capability + 1) h
  omega

end FiniteCapabilityGrowth
end DistinctionSelfReference
