import DistinctionSelfReference.RSIDependencyGraph
import DistinctionSelfReference.AdvancedRSIDependencyGraph
import DistinctionSelfReference.NextRSIDependencyGraph

namespace DistinctionSelfReference
namespace RSIInvariantCore

/--
Common semantic roles used to compare frameworks whose concrete condition
languages are different.
-/
inductive Role
  | trustAnchor
  | soundnessTransfer
  | validationEvidence
  deriving DecidableEq, Repr

def guardedMap : RSIDependencyGraph.Condition → Role
  | .verifierSoundness => .trustAnchor
  | .verifierRefinement => .soundnessTransfer
  | _ => .trustAnchor

def advancedMap : AdvancedRSIDependencyGraph.Condition → Role
  | .oldVerifierSoundness => .trustAnchor
  | .trustedKernelSoundness => .trustAnchor
  | .explicitProofObject => .validationEvidence
  | .proofChecking => .soundnessTransfer
  | _ => .trustAnchor

def nextMap : NextRSIDependencyGraph.Condition → Role
  | .initialKernelTrust => .trustAnchor
  | .predecessorCheckedMigration => .soundnessTransfer
  | .kernelTrustImpliesSoundness => .soundnessTransfer
  | _ => .trustAnchor

/-- Role summary of conservative verifier migration. -/
def guardedRoles : Set Role :=
  {r | r = .trustAnchor ∨ r = .soundnessTransfer}

/-- Role summary of proof-checked verifier expansion. -/
def proofCheckedRoles : Set Role :=
  {r | r = .trustAnchor ∨ r = .soundnessTransfer ∨ r = .validationEvidence}

/-- Role summary of predecessor-checked kernel migration. -/
def predecessorRoles : Set Role :=
  {r | r = .trustAnchor ∨ r = .soundnessTransfer}

/--
Every concrete condition required by conservative verifier migration maps into
its target role summary.
-/
theorem guarded_translation_covers_target
    (c : RSIDependencyGraph.Condition)
    (hc : c ∈ RSIDependencyGraph.required
      RSIDependencyGraph.Capability.trustedVerifierMigration) :
    guardedMap c ∈ guardedRoles := by
  change c = .verifierSoundness ∨ c = .verifierRefinement at hc
  rcases hc with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Proof-checked expansion translates to anchor, transfer, or evidence roles. -/
theorem proofChecked_translation_covers_target
    (c : AdvancedRSIDependencyGraph.Condition)
    (hc : c ∈ AdvancedRSIDependencyGraph.required
      AdvancedRSIDependencyGraph.Capability.proofCheckedVerifierExpansion) :
    advancedMap c ∈ proofCheckedRoles := by
  change c = .oldVerifierSoundness ∨
    c = .explicitProofObject ∨
    c = .trustedKernelSoundness ∨
    c = .proofChecking at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)

/-- Predecessor migration translates to the anchor/transfer role summary. -/
theorem predecessor_translation_covers_target
    (c : NextRSIDependencyGraph.Condition)
    (hc : c ∈ NextRSIDependencyGraph.required
      NextRSIDependencyGraph.Capability.trustedKernelMigration) :
    nextMap c ∈ predecessorRoles := by
  change c = .predecessorCheckedMigration ∨
    c = .initialKernelTrust ∨
    c = .kernelTrustImpliesSoundness at hc
  rcases hc with rfl | rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/--
First M5-style invariant core across three distinct trust architectures.
The intersection is taken only after translating into shared semantic roles.
-/
def trustCore : Set Role :=
  fun r =>
    r ∈ guardedRoles ∧
    r ∈ proofCheckedRoles ∧
    r ∈ predecessorRoles

theorem trustCore_exact (r : Role) :
    r ∈ trustCore ↔
      r = Role.trustAnchor ∨ r = Role.soundnessTransfer := by
  constructor
  · intro h
    exact h.1
  · intro h
    rcases h with rfl | rfl
    · exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
    · exact ⟨Or.inr rfl, Or.inr (Or.inl rfl), Or.inr rfl⟩

theorem trustAnchor_in_core :
    Role.trustAnchor ∈ trustCore := by
  exact (trustCore_exact Role.trustAnchor).2 (Or.inl rfl)

theorem soundnessTransfer_in_core :
    Role.soundnessTransfer ∈ trustCore := by
  exact (trustCore_exact Role.soundnessTransfer).2 (Or.inr rfl)

theorem evidence_not_in_core :
    Role.validationEvidence ∉ trustCore := by
  intro h
  rcases (trustCore_exact Role.validationEvidence).1 h with h | h
  · cases h
  · cases h

/--
Validation evidence is architecture-specific in this first comparison, while a
trust anchor and a soundness-transfer mechanism survive all three translations.
-/
theorem core_has_two_roles :
    ∀ r, r ∈ trustCore ↔
      r = Role.trustAnchor ∨ r = Role.soundnessTransfer :=
  trustCore_exact

end RSIInvariantCore
end DistinctionSelfReference
