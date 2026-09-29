import Mathlib.Data.Set.Basic

namespace DistinctionSelfReference
namespace TrustDelegation

universe u v

/--
A delegation protocol for self-modifying checker versions.
Soundness is abstract here so the protocol can be instantiated by verifier
soundness, trusted-kernel soundness, or another invariant-relative criterion.
-/
structure Protocol (KernelVersion : Type u) where
  DelegationProof : Type v
  Sound : KernelVersion → Prop
  Compromised : KernelVersion → Prop
  checkDelegation :
    KernelVersion → KernelVersion → DelegationProof → Bool
  delegationSound :
    ∀ checker new proof,
      ¬ Compromised checker →
      Sound checker →
      checkDelegation checker new proof = true →
      Sound new

namespace Protocol

variable {KernelVersion : Type u}

def Healthy
    (P : Protocol.{u, v} KernelVersion)
    (k : KernelVersion) : Prop :=
  ¬ P.Compromised k ∧ P.Sound k

/-- Both overlapping checkers approve the same successor checker. -/
def DualApproved
    (P : Protocol.{u, v} KernelVersion)
    (left right new : KernelVersion) : Prop :=
  ∃ leftProof rightProof,
    P.checkDelegation left new leftProof = true ∧
    P.checkDelegation right new rightProof = true

theorem new_sound_of_dual_of_leftHealthy
    (P : Protocol.{u, v} KernelVersion)
    {left right new : KernelVersion}
    (hdual : P.DualApproved left right new)
    (hleft : P.Healthy left) :
    P.Sound new := by
  rcases hdual with ⟨leftProof, rightProof, hleftCheck, hrightCheck⟩
  exact P.delegationSound left new leftProof
    hleft.1 hleft.2 hleftCheck

theorem new_sound_of_dual_of_rightHealthy
    (P : Protocol.{u, v} KernelVersion)
    {left right new : KernelVersion}
    (hdual : P.DualApproved left right new)
    (hright : P.Healthy right) :
    P.Sound new := by
  rcases hdual with ⟨leftProof, rightProof, hleftCheck, hrightCheck⟩
  exact P.delegationSound right new rightProof
    hright.1 hright.2 hrightCheck

/--
Dual overlap permits recovery from one compromised predecessor as long as one
overlapping checker remains healthy and approved the successor.
-/
theorem new_sound_of_dual_of_oneHealthy
    (P : Protocol.{u, v} KernelVersion)
    {left right new : KernelVersion}
    (hdual : P.DualApproved left right new)
    (healthy : P.Healthy left ∨ P.Healthy right) :
    P.Sound new := by
  rcases healthy with hleft | hright
  · exact P.new_sound_of_dual_of_leftHealthy hdual hleft
  · exact P.new_sound_of_dual_of_rightHealthy hdual hright

end Protocol

/-- Explicit trust-set expansion and revocation are kept separate from soundness. -/
def expandTrust {KernelVersion : Type u}
    (trusted : Set KernelVersion) (new : KernelVersion) :
    Set KernelVersion :=
  insert new trusted

def revokeTrust {KernelVersion : Type u}
    (trusted : Set KernelVersion) (old : KernelVersion) :
    Set KernelVersion :=
  trusted \ {old}

theorem new_mem_expandTrust
    {KernelVersion : Type u}
    (trusted : Set KernelVersion) (new : KernelVersion) :
    new ∈ expandTrust trusted new := by
  change new = new ∨ new ∈ trusted
  exact Or.inl rfl

theorem revoke_preserves_other
    {KernelVersion : Type u}
    {trusted : Set KernelVersion}
    {old new : KernelVersion}
    (hne : new ≠ old)
    (hnew : new ∈ trusted) :
    new ∈ revokeTrust trusted old := by
  refine ⟨hnew, ?_⟩
  intro h
  exact hne (by simpa using h)

namespace Example

def protocol : Protocol Nat where
  DelegationProof := Unit
  Sound := fun _ => True
  Compromised := fun k => k = 0
  checkDelegation := fun _ _ _ => true
  delegationSound := by
    intro checker new proof hhealthy hsound hcheck
    trivial

theorem primary_compromised :
    protocol.Compromised 0 := by
  rfl

theorem backup_healthy :
    protocol.Healthy 1 := by
  constructor
  · simp [protocol]
  · trivial

theorem dual_approves_new :
    protocol.DualApproved 0 1 2 := by
  exact ⟨Unit.unit, Unit.unit, rfl, rfl⟩

/-- The uncompromised overlapping backup can justify a successor after primary compromise. -/
theorem recovery_sound :
    protocol.Sound 2 := by
  exact protocol.new_sound_of_dual_of_oneHealthy
    dual_approves_new (Or.inr backup_healthy)

end Example
end TrustDelegation
end DistinctionSelfReference
