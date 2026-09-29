import DistinctionSelfReference.FeasibleFramework
import DistinctionSelfReference.NextRSIDependencyGraph
import DistinctionSelfReference.FullVersionDiagnostics
import DistinctionSelfReference.IndefiniteCallability
import DistinctionSelfReference.TrustedKernelMigration
import DistinctionSelfReference.JointRSIConvergence

namespace DistinctionSelfReference
namespace NextRSIFeasibility

open MetaFramework
open NextRSIDependencyGraph
open SelfModification
open TrustedKernel
open KernelVerificationResources
open LongRunRSI

/-- Concrete proof-checking model with uniformly bounded checking cost. -/
def callKernel : Kernel Nat where
  Proof := Unit
  check := fun _ _ => true

def callCost : CostModel callKernel where
  cost := fun _ _ => 1

def callProposals (n : Nat) : Proposal Nat where
  before := n
  after := n + 1

def callBudget (_ : Nat) : Nat := 1

theorem call_uniform_bound :
    ∀ n, ∃ proof,
      callKernel.check (callProposals n) proof = true ∧
        callCost.cost (callProposals n) proof ≤ 1 := by
  intro n
  exact ⟨Unit.unit, rfl, le_rfl⟩

theorem call_budget_covers :
    ∀ n, 1 ≤ callBudget n := by
  intro n
  rfl

/-- Constant sequences witness the three convergence conditions. -/
def capTarget : CapabilityOrder.Profile Bool := ⟨{false}⟩
def capSeq (_ : Nat) : CapabilityOrder.Profile Bool := capTarget
def kernelSeq (_ : Nat) : Bool := false
def requirementSeq (_ : Nat) : Bool := false
def retainedSeq (_ : Nat) : Bool := false

theorem cap_converges :
    EventuallyConstant capSeq capTarget := by
  exact ⟨0, by intro n hn; rfl⟩

theorem kernel_converges :
    EventuallyConstant kernelSeq false := by
  exact ⟨0, by intro n hn; rfl⟩

theorem requirement_converges :
    EventuallyConstant requirementSeq false := by
  exact ⟨0, by intro n hn; rfl⟩

theorem fixed_lag_tracks :
    JointRSIConvergence.TracksWithLag 1 requirementSeq retainedSeq := by
  intro n
  rfl

/--
One concrete realization simultaneously satisfies every next-phase condition
except strict growth inside the deliberately recurrent full-version example.
-/
def semantics : ConditionSemantics Condition where
  Realization := Unit
  holds _ c :=
    match c with
    | .pointwiseNonDegradation =>
        ∀ x, x.profile ≤
          (FullVersionDiagnostics.Example.togglePayload.propose x).profile
    | .fullVersionRecurrence =>
        FullVersionDiagnostics.Recurrent
          FullVersionDiagnostics.Example.togglePayload
          FullVersionDiagnostics.Example.start
    | .strictFirstCapabilityGrowth =>
        CapabilityDynamics.StrictGrowth
          FullVersionDiagnostics.Example.start.profile
          (FullVersionDiagnostics.Example.togglePayload.propose
            FullVersionDiagnostics.Example.start).profile
    | .uniformProofCostBound =>
        ∀ n, ∃ proof,
          callKernel.check (callProposals n) proof = true ∧
            callCost.cost (callProposals n) proof ≤ 1
    | .budgetCoverage => ∀ n, 1 ≤ callBudget n
    | .predecessorCheckedMigration =>
        TrustedKernelMigration.Protocol.Example.protocol.MigrationChain
          TrustedKernelMigration.Protocol.Example.versions
    | .initialKernelTrust =>
        TrustedKernelMigration.Protocol.Example.protocol.Trusted
          (TrustedKernelMigration.Protocol.Example.versions 0)
    | .kernelTrustImpliesSoundness =>
        ∀ n,
          (TrustedKernelMigration.Protocol.Example.protocol.proposalKernel
            (TrustedKernelMigration.Protocol.Example.versions n)).SoundFor
            TrustedKernelMigration.Protocol.Example.protocol.Invariant
    | .capabilityConvergence => EventuallyConstant capSeq capTarget
    | .kernelVersionConvergence => EventuallyConstant kernelSeq false
    | .requirementConvergence => EventuallyConstant requirementSeq false
    | .fixedLagRealityTracking =>
        JointRSIConvergence.TracksWithLag 1 requirementSeq retainedSeq

theorem holds_of_not_strict
    (c : Condition)
    (hne : c ≠ Condition.strictFirstCapabilityGrowth) :
    semantics.holds Unit.unit c := by
  cases c with
  | pointwiseNonDegradation =>
      exact FullVersionDiagnostics.Example.pointwise_nonDegrading
  | fullVersionRecurrence =>
      exact FullVersionDiagnostics.Example.recurrent
  | strictFirstCapabilityGrowth =>
      exact (hne rfl).elim
  | uniformProofCostBound => exact call_uniform_bound
  | budgetCoverage => exact call_budget_covers
  | predecessorCheckedMigration =>
      exact TrustedKernelMigration.Protocol.Example.migrationChain
  | initialKernelTrust => trivial
  | kernelTrustImpliesSoundness =>
      exact TrustedKernelMigration.Protocol.Example.all_proposal_kernels_sound
  | capabilityConvergence => exact cap_converges
  | kernelVersionConvergence => exact kernel_converges
  | requirementConvergence => exact requirement_converges
  | fixedLagRealityTracking => exact fixed_lag_tracks

theorem strict_not_required (cap : Capability) :
    Condition.strictFirstCapabilityGrowth ∉ required cap := by
  cases cap <;> simp [required]

theorem required_compatible (cap : Capability) :
    semantics.Compatible (required cap) := by
  refine ⟨Unit.unit, ?_⟩
  intro c hc
  apply holds_of_not_strict c
  intro heq
  subst c
  exact strict_not_required cap hc

theorem required_feasible_minimal (cap : Capability) :
    FeasibleInclusionMinimal graph semantics
      (required cap) {cap} := by
  apply feasibleInclusionMinimal_of_inclusionMinimal_of_compatible
  · exact required_minimal cap
  · exact required_compatible cap

end NextRSIFeasibility
end DistinctionSelfReference
