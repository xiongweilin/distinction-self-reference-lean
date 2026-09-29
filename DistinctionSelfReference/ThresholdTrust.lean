import Mathlib.Data.Finset.Card
import DistinctionSelfReference.TrustDelegation

namespace DistinctionSelfReference
namespace ThresholdTrust

open TrustDelegation

universe u v

namespace TrustDelegation.Protocol

variable {KernelVersion : Type u}

/-- A finite set of checker versions all approving the same successor. -/
structure QuorumApproval
    (P : Protocol.{u, v} KernelVersion)
    (new : KernelVersion)
    [DecidableEq KernelVersion] where
  voters : Finset KernelVersion
  proofOf : KernelVersion → P.DelegationProof
  checked :
    ∀ checker, checker ∈ voters →
      P.checkDelegation checker new (proofOf checker) = true

/--
If an approving quorum has at least threshold members but fewer than threshold
of those approvers are compromised, at least one approver is healthy. That one
healthy approval is enough to transfer soundness to the successor.
-/
theorem sound_of_quorum
    (P : Protocol.{u, v} KernelVersion)
    [DecidableEq KernelVersion]
    [DecidablePred P.Compromised]
    {new : KernelVersion}
    (q : QuorumApproval P new)
    (threshold : Nat)
    (hsize : threshold ≤ q.voters.card)
    (hbad : (q.voters.filter P.Compromised).card < threshold)
    (hsound :
      ∀ checker, checker ∈ q.voters →
        ¬ P.Compromised checker → P.Sound checker) :
    P.Sound new := by
  have hex :
      ∃ checker, checker ∈ q.voters ∧ ¬ P.Compromised checker := by
    by_cases h :
        ∃ checker, checker ∈ q.voters ∧ ¬ P.Compromised checker
    · exact h
    · have hall :
          ∀ checker ∈ q.voters, P.Compromised checker := by
        intro checker hmem
        by_contra hcomp
        exact h ⟨checker, hmem, hcomp⟩
      have hfilter :
          q.voters.filter P.Compromised = q.voters :=
        Finset.filter_eq_self.2 hall
      rw [hfilter] at hbad
      exact (Nat.not_lt_of_ge hsize hbad).elim
  rcases hex with ⟨checker, hmem, hhealthy⟩
  exact P.delegationSound checker new (q.proofOf checker)
    hhealthy (hsound checker hmem hhealthy) (q.checked checker hmem)

end TrustDelegation.Protocol

namespace QuorumOnlyCounterexample

def check (checker new : Nat) (_ : Unit) : Bool :=
  if checker < 2 then true else decide (new ≠ 2)

def protocol : TrustDelegation.Protocol Nat where
  DelegationProof := Unit
  Sound := fun k => k ≠ 2
  Compromised := fun k => k < 2
  checkDelegation := check
  delegationSound := by
    intro checker new proof hhealthy hsound hcheck
    simp [check, hhealthy] at hcheck
    exact hcheck

instance : DecidablePred protocol.Compromised := by
  intro k
  simp [protocol]
  infer_instance

def badQuorum :
    TrustDelegation.Protocol.QuorumApproval protocol 2 where
  voters := {0, 1}
  proofOf := fun _ => Unit.unit
  checked := by
    intro checker hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · rfl
    · rfl

theorem quorum_size_two :
    2 ≤ badQuorum.voters.card := by
  decide

theorem successor_unsound :
    ¬ protocol.Sound 2 := by
  simp [protocol]

/--
Approval count by itself is insufficient: a full quorum consisting entirely
of compromised checkers can approve an unsound successor.
-/
theorem quorum_without_health_not_sufficient :
    2 ≤ badQuorum.voters.card ∧ ¬ protocol.Sound 2 :=
  ⟨quorum_size_two, successor_unsound⟩

end QuorumOnlyCounterexample
end ThresholdTrust
end DistinctionSelfReference
