import DistinctionSelfReference.SelfModification

namespace DistinctionSelfReference
namespace VerifierMigration

open SelfModification

universe u

variable {Version : Type u}

/--
A new verifier refines an old verifier when every proposal newly accepted was
already accepted by the old trusted verifier.
-/
def Refines
    (new old : Verifier Version) : Prop :=
  ∀ p, new.accepts p → old.accepts p

theorem refines_refl (V : Verifier Version) :
    Refines V V := by
  intro p hp
  exact hp

theorem refines_trans
    {new mid old : Verifier Version}
    (hnm : Refines new mid)
    (hmo : Refines mid old) :
    Refines new old := by
  intro p hp
  exact hmo p (hnm p hp)

/--
Verifier refinement transports soundness without asking the new verifier to
prove its own soundness.
-/
theorem soundness_preserved
    {new old : Verifier Version}
    {Invariant : Version → Prop}
    (hrefine : Refines new old)
    (hsound : old.SoundFor Invariant) :
    new.SoundFor Invariant := by
  intro p hp
  exact hsound p (hrefine p hp)

/-- A migration chain refines each next verifier against its predecessor. -/
def MigrationChain
    (chain : ℕ → Verifier Version) : Prop :=
  ∀ n, Refines (chain (n + 1)) (chain n)

theorem refines_initial
    {chain : ℕ → Verifier Version}
    (hchain : MigrationChain chain) :
    ∀ n, Refines (chain n) (chain 0) := by
  intro n
  induction n with
  | zero => exact refines_refl (chain 0)
  | succ n ih =>
      exact refines_trans (hchain n) ih

/-- Soundness of the initial trusted verifier propagates through the chain. -/
theorem soundness_along_chain
    {chain : ℕ → Verifier Version}
    (hchain : MigrationChain chain)
    (Invariant : Version → Prop)
    (hzero : (chain 0).SoundFor Invariant) :
    ∀ n, (chain n).SoundFor Invariant := by
  intro n
  exact soundness_preserved (refines_initial hchain n) hzero

end VerifierMigration
end DistinctionSelfReference
