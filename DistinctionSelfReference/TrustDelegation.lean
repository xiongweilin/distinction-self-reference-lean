import DistinctionSelfReference.TrustedKernel

namespace DistinctionSelfReference
namespace TrustDelegation

open SelfModification
open TrustedKernel

universe u v w

/--
A delegation protocol in which checker versions can themselves be compromised.
A healthy checker is both uncompromised and sound for the protected invariant.
-/
structure Protocol
    (KernelVersion : Type u) (Version : Type v) where
  DelegationProof : Type w
  proposalKernel : KernelVersion → Kernel Version
  Invariant : Version → Prop
  Compromised : KernelVersion → Prop
  checkDelegation :
    KernelVersion → KernelVersion → DelegationProof → Bool
  delegationSound :
    ∀ checker new proof,
      ¬ Compromised checker →
      (proposalKernel checker).SoundFor Invariant →
      checkDelegation checker new proof = true →
      (proposalKernel new).SoundFor Invariant

namespace Protocol

variable {KernelVersion : Type u} {Version : Type v}

def Healthy
    (P : Protocol.{u, v, w} KernelVersion Version)
    (k : KernelVersion) : Prop :=
  ¬ P.Compromised k ∧ (P.proposalKernel k).SoundFor P.Invariant

/-- Both overlapping checkers approve the same successor checker. -/
def DualApproved
    (P : Protocol.{u, v, w} KernelVersion Version)
    (left right new : KernelVersion) : Prop :=
  ∃ leftProof rightProof,
    P.checkDelegation left new leftProof = true ∧
    P.checkDelegation right new rightProof = true

theorem new_sound_of_dual_of_leftHealthy
    (P : Protocol.{u, v, w} KernelVersion Version)
    {left right new : KernelVersion}
    (hdual : P.DualApproved left right new)
    (hleft : P.Healthy left) :
    (P.proposalKernel new).SoundFor P.Invariant := by
  rcases hdual with ⟨leftProof, rightProof, hleftCheck, hrightCheck⟩
  exact P.delegationSound left new leftProof
    hleft.1 hleft.2 hleftCheck

theorem new_sound_of_dual_of_rightHealthy
    (P : Protocol.{u, v, w} KernelVersion Version)
    {left right new : KernelVersion}
    (hdual : P.DualApproved left right new)
    (hright : P.Healthy right) :
    (P.proposalKernel new).SoundFor P.Invariant := by
  rcases hdual with ⟨leftProof, rightProof, hleftCheck, hrightCheck⟩
  exact P.delegationSound right new rightProof
    hright.1 hright.2 hrightCheck

/--
Dual overlap permits recovery from one compromised predecessor as long as one
overlapping checker remains healthy and approved the successor.
-/
theorem new_sound_of_dual_of_oneHealthy
    (P : Protocol.{u, v, w} KernelVersion Version)
    {left right new : KernelVersion}
    (hdual : P.DualApproved left right new)
    (healthy : P.Healthy left ∨ P.Healthy right) :
    (P.proposalKernel new).SoundFor P.Invariant := by
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
  simp [expandTrust]

theorem revoke_preserves_other
    {KernelVersion : Type u}
    {trusted : Set KernelVersion}
    {old new : KernelVersion}
    (hne : new ≠ old)
    (hnew : new ∈ trusted) :
    new ∈ revokeTrust trusted old := by
  exact ⟨hnew, by simpa [hne]⟩

namespace Example

def kernel (_ : Nat) : Kernel Bool where
  Proof := Unit
  check := fun _ _ => true

def protocol : Protocol Nat Bool where
  DelegationProof := Unit
  proposalKernel := kernel
  Invariant := fun _ => True
  Compromised := fun k => k = 0
  checkDelegation := fun _ _ _ => true
  delegationSound := by
    intro checker new proof hhealthy hsound hcheck
    intro p hp
    trivial

theorem primary_compromised :
    protocol.Compromised 0 := by
  rfl

theorem backup_healthy :
    protocol.Healthy 1 := by
  constructor
  · simp [protocol]
  · intro p hp
    trivial

theorem dual_approves_new :
    protocol.DualApproved 0 1 2 := by
  exact ⟨Unit.unit, Unit.unit, rfl, rfl⟩

/-- The uncompromised overlapping backup can justify a successor after primary compromise. -/
theorem recovery_sound :
    (protocol.proposalKernel 2).SoundFor protocol.Invariant := by
  exact protocol.new_sound_of_dual_of_oneHealthy
    dual_approves_new (Or.inr backup_healthy)

end Example
end TrustDelegation
end DistinctionSelfReference
