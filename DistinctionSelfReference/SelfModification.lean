import DistinctionSelfReference.CapabilityOrder

namespace DistinctionSelfReference
namespace SelfModification

open CapabilityOrder

universe u v

/-- A proposed transition from one system version to another. -/
structure Proposal (Version : Type u) where
  before : Version
  after : Version

/-- A verifier decides whether a proposed modification is admissible. -/
structure Verifier (Version : Type u) where
  accepts : Proposal Version → Prop

namespace Verifier

variable {Version : Type u}

/-- Soundness relative to an invariant on versions. -/
def SoundFor
    (V : Verifier Version)
    (Invariant : Version → Prop) : Prop :=
  ∀ p, V.accepts p → Invariant p.after

theorem accepted_preserves
    (V : Verifier Version)
    (Invariant : Version → Prop)
    (hsound : V.SoundFor Invariant)
    (p : Proposal Version)
    (haccept : V.accepts p) :
    Invariant p.after :=
  hsound p haccept

end Verifier

/-- A self-modifier proposes a successor version from the current version. -/
structure Modifier (Version : Type u) where
  propose : Version → Version

namespace Modifier

variable {Version : Type u}

/-- The concrete proposal generated from one current version. -/
def proposal (M : Modifier Version) (current : Version) : Proposal Version where
  before := current
  after := M.propose current

/-- One verified self-modification step. -/
def VerifiedStep
    (M : Modifier Version)
    (V : Verifier Version)
    (current next : Version) : Prop :=
  next = M.propose current ∧ V.accepts (M.proposal current)

theorem verifiedStep_preserves_invariant
    (M : Modifier Version)
    (V : Verifier Version)
    (Invariant : Version → Prop)
    (hsound : V.SoundFor Invariant)
    {current next : Version}
    (hstep : M.VerifiedStep V current next) :
    Invariant next := by
  rcases hstep with ⟨rfl, haccept⟩
  exact hsound (M.proposal current) haccept

end Modifier

/--
A capability-aware version separates internal version identity from the
extensional capability profile used for comparison.
-/
structure CapVersion (Capability : Type u) (Payload : Type v) where
  payload : Payload
  profile : CapabilityOrder.Profile Capability

namespace CapVersion

variable {Capability : Type u} {Payload : Type v}

/-- A modification is non-degrading when it never loses an existing capability. -/
def NonDegrading
    (p : Proposal (CapVersion Capability Payload)) : Prop :=
  p.before.profile ≤ p.after.profile

/-- Strict improvement additionally requires a strict capability increase. -/
def StrictImprovement
    (p : Proposal (CapVersion Capability Payload)) : Prop :=
  p.before.profile < p.after.profile

end CapVersion

/--
A verifier that is sound for both a semantic invariant and non-degradation
guarantees both properties on every accepted proposal.
-/
theorem accepted_preserves_invariant_and_capability
    {Capability : Type u} {Payload : Type v}
    (V : Verifier (CapVersion Capability Payload))
    (Invariant : CapVersion Capability Payload → Prop)
    (hinv : V.SoundFor Invariant)
    (hcap : ∀ p, V.accepts p → CapVersion.NonDegrading p)
    (p : Proposal (CapVersion Capability Payload))
    (haccept : V.accepts p) :
    Invariant p.after ∧ p.before.profile ≤ p.after.profile := by
  exact ⟨hinv p haccept, hcap p haccept⟩

end SelfModification
end DistinctionSelfReference
