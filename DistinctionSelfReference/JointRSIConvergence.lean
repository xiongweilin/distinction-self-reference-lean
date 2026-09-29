import DistinctionSelfReference.LongRunRSI
import DistinctionSelfReference.TrustedKernelMigration

namespace DistinctionSelfReference
namespace JointRSIConvergence

open CapabilityOrder
open LongRunRSI

universe u v w

/-- A retained boundary tracks each requirement after one fixed finite lag. -/
def TracksWithLag
    {Boundary : Type u}
    (lag : Nat)
    (required retained : Nat → Boundary) : Prop :=
  ∀ n, retained (n + lag) = required n

/-- Exact tracking is the zero-lag special case. -/
theorem tracksWithLag_zero
    {Boundary : Type u}
    {required retained : Nat → Boundary}
    (h : ∀ n, retained n = required n) :
    TracksWithLag 0 required retained := by
  intro n
  simpa using h n

/--
If requirements stabilize, any fixed-lag tracker stabilizes after the same
index in the lag-shifted observation frame.
-/
theorem shifted_retained_converges
    {Boundary : Type u}
    {required retained : Nat → Boundary}
    {target : Boundary}
    (lag : Nat)
    (htrack : TracksWithLag lag required retained)
    (hreq : EventuallyConstant required target) :
    EventuallyConstant (fun n => retained (n + lag)) target := by
  rcases hreq with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  rw [htrack n]
  exact hN n hn

/-- Trust-version convergence is kept separate from semantic kernel soundness. -/
def TrustConverges
    {KernelVersion : Type u}
    (versions : Nat → KernelVersion)
    (target : KernelVersion) : Prop :=
  EventuallyConstant versions target

/-- Capability, trust-version, and reality-boundary convergence compose. -/
theorem joint_three_converges
    {Capability : Type u}
    {KernelVersion : Type v}
    {Boundary : Type w}
    {caps : Nat → Profile Capability}
    {kernels : Nat → KernelVersion}
    {boundary : Nat → Boundary}
    {capTarget : Profile Capability}
    {kernelTarget : KernelVersion}
    {boundaryTarget : Boundary}
    (hcaps : EventuallyConstant caps capTarget)
    (hkernels : EventuallyConstant kernels kernelTarget)
    (hboundary : EventuallyConstant boundary boundaryTarget) :
    EventuallyConstant
      (fun n => (caps n, kernels n, boundary n))
      (capTarget, kernelTarget, boundaryTarget) := by
  rcases hcaps with ⟨Nc, hc⟩
  rcases hkernels with ⟨Nk, hk⟩
  rcases hboundary with ⟨Nb, hb⟩
  refine ⟨max Nc (max Nk Nb), ?_⟩
  intro n hn
  have hnc : Nc ≤ n := le_trans (le_max_left _ _) hn
  have hrest : max Nk Nb ≤ n := le_trans (le_max_right _ _) hn
  have hnk : Nk ≤ n := le_trans (le_max_left _ _) hrest
  have hnb : Nb ≤ n := le_trans (le_max_right _ _) hrest
  simp [hc n hnc, hk n hnk, hb n hnb]

/-- Fixed-lag reality tracking can be combined with trust and capability convergence. -/
theorem joint_with_fixed_lag_reality
    {Capability : Type u}
    {KernelVersion : Type v}
    {Boundary : Type w}
    {caps : Nat → Profile Capability}
    {kernels : Nat → KernelVersion}
    {required retained : Nat → Boundary}
    {capTarget : Profile Capability}
    {kernelTarget : KernelVersion}
    {boundaryTarget : Boundary}
    (lag : Nat)
    (hcaps : EventuallyConstant caps capTarget)
    (hkernels : EventuallyConstant kernels kernelTarget)
    (hrequired : EventuallyConstant required boundaryTarget)
    (htrack : TracksWithLag lag required retained) :
    EventuallyConstant
      (fun n => (caps n, kernels n, retained (n + lag)))
      (capTarget, kernelTarget, boundaryTarget) := by
  exact joint_three_converges hcaps hkernels
    (shifted_retained_converges lag htrack hrequired)

end JointRSIConvergence
end DistinctionSelfReference
