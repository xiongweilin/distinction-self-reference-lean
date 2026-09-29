import DistinctionSelfReference.VerifierMigration

namespace DistinctionSelfReference
namespace CertifiedVerifierExpansion

open SelfModification
open VerifierMigration

universe u

variable {Version : Type u}

/--
An external certificate authority can validate proposals independently of the
current verifier. Soundness is stated against the same semantic invariant.
-/
structure Authority (Version : Type u) where
  certifies : Proposal Version → Prop

namespace Authority

def SoundFor
    (A : Authority Version)
    (Invariant : Version → Prop) : Prop :=
  ∀ p, A.certifies p → Invariant p.after

end Authority

/--
Certified expansion accepts everything the old verifier accepted plus every
proposal carrying an authority certificate.
-/
def expand
    (old : Verifier Version)
    (A : Authority Version) :
    Verifier Version where
  accepts p := old.accepts p ∨ A.certifies p

theorem old_acceptance_preserved
    (old : Verifier Version)
    (A : Authority Version)
    (p : Proposal Version)
    (h : old.accepts p) :
    (expand old A).accepts p :=
  Or.inl h

theorem certified_acceptance_added
    (old : Verifier Version)
    (A : Authority Version)
    (p : Proposal Version)
    (h : A.certifies p) :
    (expand old A).accepts p :=
  Or.inr h

/--
Safe expansion theorem: the acceptance domain may grow, while soundness is
preserved if both the old verifier and the external certificate authority are
sound for the same invariant.
-/
theorem expansion_sound
    (old : Verifier Version)
    (A : Authority Version)
    (Invariant : Version → Prop)
    (hold : old.SoundFor Invariant)
    (hcert : A.SoundFor Invariant) :
    (expand old A).SoundFor Invariant := by
  intro p hp
  rcases hp with hp | hp
  · exact hold p hp
  · exact hcert p hp

/--
Conservative verifier refinement runs opposite to genuine acceptance expansion:
an expansion refines the old verifier only when certificates add nothing new.
-/
theorem expansion_refines_old_iff
    (old : Verifier Version)
    (A : Authority Version) :
    Refines (expand old A) old ↔
      ∀ p, A.certifies p → old.accepts p := by
  constructor
  · intro href p hcert
    exact href p (Or.inr hcert)
  · intro h p hp
    rcases hp with hp | hp
    · exact hp
    · exact h p hp

/-- Tiny model witnessing strict but sound verifier expansion. -/
namespace Example

def invariant (_ : Bool) : Prop := True

def old : Verifier Bool where
  accepts p := p.after = false

def authority : Authority Bool where
  certifies p := p.after = true

def added : Proposal Bool where
  before := false
  after := true

theorem old_sound : old.SoundFor invariant := by
  intro _ _
  trivial

theorem authority_sound : authority.SoundFor invariant := by
  intro _ _
  trivial

theorem expanded_sound :
    (expand old authority).SoundFor invariant :=
  expansion_sound old authority invariant old_sound authority_sound

theorem expanded_accepts_added :
    (expand old authority).accepts added := by
  exact Or.inr rfl

theorem old_rejects_added :
    ¬ old.accepts added := by
  intro h
  change true = false at h
  exact Bool.false_ne_true h.symm

theorem expansion_is_strict :
    ∃ p, (expand old authority).accepts p ∧ ¬ old.accepts p :=
  ⟨added, expanded_accepts_added, old_rejects_added⟩

theorem expansion_not_conservative :
    ¬ Refines (expand old authority) old := by
  intro href
  exact old_rejects_added (href added expanded_accepts_added)

end Example
end CertifiedVerifierExpansion
end DistinctionSelfReference
