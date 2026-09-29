import DistinctionSelfReference.CapabilityDynamics

namespace DistinctionSelfReference
namespace FullVersionDiagnostics

open CapabilityOrder
open SelfModification
open CapabilityDynamics

universe u v

variable {Capability : Type u} {Payload : Type v}

def orbit
    (M : Modifier (CapVersion Capability Payload))
    (start : CapVersion Capability Payload) :
    Nat → CapVersion Capability Payload
  | 0 => start
  | n + 1 => M.propose (orbit M start n)

@[simp] theorem orbit_zero
    (M : Modifier (CapVersion Capability Payload))
    (start : CapVersion Capability Payload) :
    orbit M start 0 = start :=
  rfl

@[simp] theorem orbit_succ
    (M : Modifier (CapVersion Capability Payload))
    (start : CapVersion Capability Payload)
    (n : Nat) :
    orbit M start (n + 1) = M.propose (orbit M start n) :=
  rfl

/-- A genuine full-version recurrence after a positive number of modifier steps. -/
def Recurrent
    (M : Modifier (CapVersion Capability Payload))
    (start : CapVersion Capability Payload) : Prop :=
  ∃ k, 0 < k ∧ orbit M start k = start

/-- A nontrivial two-cycle is recurrence without a one-step fixed point. -/
def TwoCycle
    (M : Modifier (CapVersion Capability Payload))
    (start : CapVersion Capability Payload) : Prop :=
  M.propose (M.propose start) = start ∧ M.propose start ≠ start

/-- Pointwise non-degradation makes the complete capability orbit monotone. -/
theorem profile_orbit_mono
    (M : Modifier (CapVersion Capability Payload))
    (start : CapVersion Capability Payload)
    (hnon : ∀ x, x.profile ≤ (M.propose x).profile) :
    Monotone (fun n => (orbit M start n).profile) := by
  apply CapabilityOrder.chain_mono
  intro n
  exact hnon (orbit M start n)

/-- Under non-degradation, recurrence forces a capability plateau on the cycle. -/
theorem recurrence_forces_profile_plateau
    (M : Modifier (CapVersion Capability Payload))
    (start : CapVersion Capability Payload)
    (hnon : ∀ x, x.profile ≤ (M.propose x).profile)
    {k n : Nat}
    (hcycle : orbit M start k = start)
    (hnk : n ≤ k) :
    (orbit M start n).profile = start.profile := by
  have hmono := profile_orbit_mono M start hnon
  have hforward : start.profile ≤ (orbit M start n).profile := by
    simpa using hmono (Nat.zero_le n)
  have hback : (orbit M start n).profile ≤ start.profile := by
    have h := hmono hnk
    simpa [hcycle] using h
  exact le_antisymm hback hforward

/-- No strict capability growth can occur inside a recurrent segment. -/
theorem no_strict_growth_inside_recurrence
    (M : Modifier (CapVersion Capability Payload))
    (start : CapVersion Capability Payload)
    (hnon : ∀ x, x.profile ≤ (M.propose x).profile)
    {k n : Nat}
    (hcycle : orbit M start k = start)
    (hnk : n + 1 ≤ k) :
    ¬ StrictGrowth
      (orbit M start n).profile
      (orbit M start (n + 1)).profile := by
  intro hstrict
  have hn := recurrence_forces_profile_plateau M start hnon hcycle
    (Nat.le_trans (Nat.le_succ n) hnk)
  have hnext := recurrence_forces_profile_plateau M start hnon hcycle hnk
  rw [hn, hnext] at hstrict
  exact (lt_irrefl start.profile) hstrict

/-- A full modifier fixed point is a period-one recurrence. -/
theorem fixedPoint_is_recurrent
    (M : Modifier (CapVersion Capability Payload))
    (start : CapVersion Capability Payload)
    (hfix : ModifierFixedPoint M start) :
    Recurrent M start := by
  refine ⟨1, by decide, ?_⟩
  simpa [orbit, ModifierFixedPoint] using hfix

namespace Example

def togglePayload : Modifier (CapVersion Bool Bool) where
  propose v := { v with payload := !v.payload }

def start : CapVersion Bool Bool where
  payload := false
  profile := ⟨{false}⟩

theorem pointwise_nonDegrading :
    ∀ x, x.profile ≤ (togglePayload.propose x).profile := by
  intro x
  rfl

theorem twoCycle : TwoCycle togglePayload start := by
  constructor
  · rfl
  · intro h
    have hp := congrArg CapVersion.payload h
    change true = false at hp
    exact Bool.true_ne_false hp

theorem recurrent : Recurrent togglePayload start := by
  exact ⟨2, by decide, rfl⟩

theorem not_fixed :
    ¬ ModifierFixedPoint togglePayload start := by
  exact twoCycle.2

theorem capability_plateau :
    Plateau start.profile (togglePayload.propose start).profile :=
  rfl

end Example
end FullVersionDiagnostics
end DistinctionSelfReference
