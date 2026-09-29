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

def translate {Condition : Type}
    (map : Condition → Role)
    (conditions : Set Condition) : Set Role :=
  map '' conditions

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

/-- Conservative verifier refinement translated into common roles. -/
def guardedRoles : Set Role :=
  translate guardedMap
    (RSIDependencyGraph.required
      RSIDependencyGraph.Capability.trustedVerifierMigration)

/-- Proof-checked verifier expansion translated into common roles. -/
def proofCheckedRoles : Set Role :=
  translate advancedMap
    (AdvancedRSIDependencyGraph.required
      AdvancedRSIDependencyGraph.Capability.proofCheckedVerifierExpansion)

/-- Predecessor-checked kernel migration translated into common roles. -/
def predecessorRoles : Set Role :=
  translate nextMap
    (NextRSIDependencyGraph.required
      NextRSIDependencyGraph.Capability.trustedKernelMigration)

theorem guardedRoles_eq :
    guardedRoles = {Role.trustAnchor, Role.soundnessTransfer} := by
  ext r
  cases r <;>
    simp [guardedRoles, translate, guardedMap,
      RSIDependencyGraph.required]

theorem proofCheckedRoles_eq :
    proofCheckedRoles =
      {Role.trustAnchor, Role.soundnessTransfer, Role.validationEvidence} := by
  ext r
  cases r <;>
    simp [proofCheckedRoles, translate, advancedMap,
      AdvancedRSIDependencyGraph.required]

theorem predecessorRoles_eq :
    predecessorRoles = {Role.trustAnchor, Role.soundnessTransfer} := by
  ext r
  cases r <;>
    simp [predecessorRoles, translate, nextMap,
      NextRSIDependencyGraph.required]

/-- First M5-style invariant core across three distinct trust architectures. -/
def trustCore : Set Role :=
  guardedRoles ∩ proofCheckedRoles ∩ predecessorRoles

theorem trustCore_exact :
    trustCore = {Role.trustAnchor, Role.soundnessTransfer} := by
  rw [trustCore, guardedRoles_eq, proofCheckedRoles_eq, predecessorRoles_eq]
  ext r
  cases r <;> simp

theorem trustAnchor_in_core :
    Role.trustAnchor ∈ trustCore := by
  rw [trustCore_exact]
  simp

theorem soundnessTransfer_in_core :
    Role.soundnessTransfer ∈ trustCore := by
  rw [trustCore_exact]
  simp

theorem evidence_not_in_core :
    Role.validationEvidence ∉ trustCore := by
  rw [trustCore_exact]
  simp

/--
The core is therefore not the literal intersection of syntax-level conditions.
It is the intersection after translation into shared semantic roles.
-/
theorem core_has_two_roles :
    ∀ r, r ∈ trustCore ↔
      r = Role.trustAnchor ∨ r = Role.soundnessTransfer := by
  intro r
  rw [trustCore_exact]
  simp [eq_comm]

end RSIInvariantCore
end DistinctionSelfReference
