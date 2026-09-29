import DistinctionSelfReference.CertifiedVerifierExpansion

namespace DistinctionSelfReference
namespace TrustedKernel

open SelfModification
open CertifiedVerifierExpansion

universe u v

/--
A small trusted proof-checking boundary. Proof objects are explicit data; the
kernel exposes only a Boolean checker.
-/
structure Kernel (Version : Type u) where
  Proof : Type v
  check : Proposal Version → Proof → Bool

namespace Kernel

variable {Version : Type u}

/-- A proposal is kernel-certified when some explicit proof object checks. -/
def Certified
    (K : Kernel.{u, v} Version)
    (p : Proposal Version) : Prop :=
  ∃ proof, K.check p proof = true

/-- Kernel soundness is the sole semantic trust obligation. -/
def SoundFor
    (K : Kernel.{u, v} Version)
    (Invariant : Version → Prop) : Prop :=
  ∀ p proof, K.check p proof = true → Invariant p.after

/-- Every trusted kernel induces the abstract certificate-authority interface. -/
def authority
    (K : Kernel.{u, v} Version) :
    Authority Version where
  certifies := K.Certified

theorem authority_sound
    (K : Kernel.{u, v} Version)
    (Invariant : Version → Prop)
    (hsound : K.SoundFor Invariant) :
    (K.authority).SoundFor Invariant := by
  intro p hp
  rcases hp with ⟨proof, hcheck⟩
  exact hsound p proof hcheck

/-- Expand an existing verifier by kernel-checked proof objects. -/
def expandVerifier
    (old : Verifier Version)
    (K : Kernel.{u, v} Version) :
    Verifier Version :=
  CertifiedVerifierExpansion.expand old K.authority

/--
Proof-checked expansion preserves soundness without the expanded verifier
endorsing itself.
-/
theorem expansion_sound
    (old : Verifier Version)
    (K : Kernel.{u, v} Version)
    (Invariant : Version → Prop)
    (hold : old.SoundFor Invariant)
    (hkernel : K.SoundFor Invariant) :
    (K.expandVerifier old).SoundFor Invariant := by
  apply CertifiedVerifierExpansion.expansion_sound
  · exact hold
  · exact K.authority_sound Invariant hkernel

theorem accepts_old
    (old : Verifier Version)
    (K : Kernel.{u, v} Version)
    (p : Proposal Version)
    (h : old.accepts p) :
    (K.expandVerifier old).accepts p :=
  Or.inl h

theorem accepts_checked
    (old : Verifier Version)
    (K : Kernel.{u, v} Version)
    (p : Proposal Version)
    (proof : K.Proof)
    (hcheck : K.check p proof = true) :
    (K.expandVerifier old).accepts p :=
  Or.inr ⟨proof, hcheck⟩

/- Concrete strict sound expansion through an explicit proof object. -/
namespace Example

def invariant (_ : Bool) : Prop := True

def old : Verifier Bool where
  accepts p := p.after = false

def kernel : Kernel Bool where
  Proof := Unit
  check p _ := p.after

def added : Proposal Bool where
  before := false
  after := true

theorem old_sound : old.SoundFor invariant := by
  intro _ _
  trivial

theorem kernel_sound : kernel.SoundFor invariant := by
  intro _ _ _
  trivial

theorem checked_added :
    kernel.check added Unit.unit = true :=
  rfl

theorem expanded_sound :
    (kernel.expandVerifier old).SoundFor invariant :=
  kernel.expansion_sound old invariant old_sound kernel_sound

theorem expanded_accepts_added :
    (kernel.expandVerifier old).accepts added :=
  kernel.accepts_checked old added Unit.unit checked_added

theorem old_rejects_added :
    ¬ old.accepts added := by
  intro h
  change true = false at h
  exact Bool.false_ne_true h.symm

theorem strict_expansion :
    ∃ p, (kernel.expandVerifier old).accepts p ∧ ¬ old.accepts p :=
  ⟨added, expanded_accepts_added, old_rejects_added⟩

end Example
end Kernel
end TrustedKernel
end DistinctionSelfReference
