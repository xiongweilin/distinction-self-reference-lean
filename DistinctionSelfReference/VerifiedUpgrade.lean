import DistinctionSelfReference.SelfModification

namespace DistinctionSelfReference
namespace VerifiedUpgrade

open CapabilityOrder
open SelfModification

universe u v

variable {Capability : Type u} {Payload : Type v}

abbrev Version := CapVersion Capability Payload

/--
A chain is accepted by a verifier when each successor is exactly the modifier's
proposal and that proposal is accepted.
-/
def VerifiedChain
    (M : Modifier (Version (Capability := Capability) (Payload := Payload)))
    (V : Verifier (Version (Capability := Capability) (Payload := Payload)))
    (chain : ℕ → Version (Capability := Capability) (Payload := Payload)) : Prop :=
  ∀ n, M.VerifiedStep V (chain n) (chain (n + 1))

/--
If every accepted proposal is non-degrading, any verified self-modification
chain is monotone in the capability order.
-/
theorem verifiedChain_capability_mono
    (M : Modifier (Version (Capability := Capability) (Payload := Payload)))
    (V : Verifier (Version (Capability := Capability) (Payload := Payload)))
    (chain : ℕ → Version (Capability := Capability) (Payload := Payload))
    (hchain : VerifiedChain M V chain)
    (hcap : ∀ p, V.accepts p → CapVersion.NonDegrading p) :
    CapabilityOrder.MonotoneChain (fun n => (chain n).profile) := by
  intro n
  have hstep := hchain n
  rcases hstep with ⟨hnext, haccept⟩
  have hnon := hcap (M.proposal (chain n)) haccept
  change (chain n).profile ≤ (chain (n + 1)).profile
  rw [hnext]
  exact hnon

/-- A sound verifier keeps the invariant true at every positive step of the chain. -/
theorem verifiedChain_invariant_after
    (M : Modifier (Version (Capability := Capability) (Payload := Payload)))
    (V : Verifier (Version (Capability := Capability) (Payload := Payload)))
    (Invariant : Version (Capability := Capability) (Payload := Payload) → Prop)
    (chain : ℕ → Version (Capability := Capability) (Payload := Payload))
    (hchain : VerifiedChain M V chain)
    (hsound : V.SoundFor Invariant) :
    ∀ n, Invariant (chain (n + 1)) := by
  intro n
  exact M.verifiedStep_preserves_invariant V Invariant hsound (hchain n)

end VerifiedUpgrade
end DistinctionSelfReference
