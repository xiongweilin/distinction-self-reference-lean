import DistinctionSelfReference.TrustedKernel

namespace DistinctionSelfReference
namespace TrustedKernelMigration

open SelfModification
open TrustedKernel

universe u v w

/--
A predecessor-checked kernel migration interface.
The current trusted checker validates an explicit handoff proof for the next
checker version; the semantic obligation is that such a checked handoff
preserves an explicit trust invariant.
-/
structure Protocol
    (KernelVersion : Type u) (Version : Type v) where
  MigrationProof : Type w
  proposalKernel : KernelVersion → Kernel.{v, w} Version
  Invariant : Version → Prop
  Trusted : KernelVersion → Prop
  checkMigration : KernelVersion → KernelVersion → MigrationProof → Bool
  handoffSound :
    ∀ old new proof,
      Trusted old →
      checkMigration old new proof = true →
      Trusted new
  trustedKernelSound :
    ∀ k, Trusted k → (proposalKernel k).SoundFor Invariant

namespace Protocol

variable {KernelVersion : Type u} {Version : Type v}

/-- Every adjacent kernel-version transition carries an explicit checked proof. -/
def MigrationChain
    (P : Protocol.{u, v, w} KernelVersion Version)
    (versions : Nat → KernelVersion) : Prop :=
  ∀ n, ∃ proof,
    P.checkMigration (versions n) (versions (n + 1)) proof = true

/-- Trust propagates indefinitely along predecessor-checked migration. -/
theorem trusted_along_chain
    (P : Protocol.{u, v, w} KernelVersion Version)
    (versions : Nat → KernelVersion)
    (hchain : P.MigrationChain versions)
    (h0 : P.Trusted (versions 0)) :
    ∀ n, P.Trusted (versions n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
      rcases hchain n with ⟨proof, hcheck⟩
      exact P.handoffSound (versions n) (versions (n + 1)) proof ih hcheck

/-- Every migrated proposal checker therefore remains sound for the invariant. -/
theorem kernel_sound_along_chain
    (P : Protocol.{u, v, w} KernelVersion Version)
    (versions : Nat → KernelVersion)
    (hchain : P.MigrationChain versions)
    (h0 : P.Trusted (versions 0)) :
    ∀ n, (P.proposalKernel (versions n)).SoundFor P.Invariant := by
  intro n
  exact P.trustedKernelSound (versions n)
    (P.trusted_along_chain versions hchain h0 n)

namespace Example

def proposalKernel (_ : Bool) : Kernel Bool where
  Proof := Unit
  check := fun _ _ => true

def protocol : Protocol Bool Bool where
  MigrationProof := Unit
  proposalKernel := proposalKernel
  Invariant := fun _ => True
  Trusted := fun _ => True
  checkMigration := fun _ _ _ => true
  handoffSound := by
    intro _ _ _ _ _
    trivial
  trustedKernelSound := by
    intro _ _ _ _ _
    trivial

def versions (n : Nat) : Bool :=
  n % 2 == 1

theorem migrationChain :
    protocol.MigrationChain versions := by
  intro n
  exact ⟨Unit.unit, rfl⟩

theorem all_kernel_versions_trusted :
    ∀ n, protocol.Trusted (versions n) :=
  protocol.trusted_along_chain versions migrationChain trivial

theorem all_proposal_kernels_sound :
    ∀ n, (protocol.proposalKernel (versions n)).SoundFor protocol.Invariant :=
  protocol.kernel_sound_along_chain versions migrationChain trivial

end Example
end Protocol
end TrustedKernelMigration
end DistinctionSelfReference
