import DistinctionSelfReference.CapabilityDynamics
import DistinctionSelfReference.IteratedReopening

namespace DistinctionSelfReference
namespace LongRunRSI

open CapabilityOrder

universe u v w

/-- Elementary discrete notion of convergence used here: eventual constancy. -/
def EventuallyConstant {α : Type u}
    (f : Nat → α) (target : α) : Prop :=
  ∃ N, ∀ n, N ≤ n → f n = target

theorem eventuallyConstant_mono_index
    {α : Type u}
    {f : Nat → α} {target : α}
    (h : EventuallyConstant f target) :
    ∃ N, ∀ n, N ≤ n → f n = target :=
  h

/-- Capability convergence means the extensional capability profile stabilizes. -/
def CapabilityConverges
    {Capability : Type u}
    (chain : Nat → Profile Capability)
    (target : Profile Capability) : Prop :=
  EventuallyConstant chain target

/-- Reality convergence means the required boundary eventually stops changing. -/
def RequirementConverges
    {World : Type u} {Boundary : Type v}
    (required : World → Boundary)
    (reality : Nat → World)
    (target : Boundary) : Prop :=
  EventuallyConstant (fun n => required (reality n)) target

/--
Exact iterated reopening turns eventual stability of reality requirements into
eventual stability of every completed update, with a one-step index shift.
-/
theorem revision_converges_of_requirement_converges
    {World : Type u} {Obs : Type v} {Boundary : Type w}
    (S : IteratedReopening.System World Obs Boundary)
    (hdetect : S.DetectsMismatch)
    (hsuccess : S.RevisionSucceeds)
    (hstable : S.RejectsFalseAlarm)
    (initial : Boundary)
    (reality : Nat → World)
    (target : Boundary)
    (hreq : RequirementConverges S.required reality target) :
    ∃ N, ∀ n, N ≤ n →
      S.trajectory initial reality (n + 1) = target := by
  rcases hreq with ⟨N, hN⟩
  exact ⟨N, fun n hn =>
    S.tracks_stable_requirement hdetect hsuccess hstable
      initial reality target N hN n hn⟩

/--
Capability convergence and reality convergence are independent hypotheses, but
when both hold their observable pair also eventually stabilizes.
-/
theorem pair_converges
    {Capability : Type u} {Boundary : Type v}
    {caps : Nat → Profile Capability}
    {boundary : Nat → Boundary}
    {capTarget : Profile Capability}
    {boundaryTarget : Boundary}
    (hcaps : EventuallyConstant caps capTarget)
    (hboundary : EventuallyConstant boundary boundaryTarget) :
    EventuallyConstant
      (fun n => (caps n, boundary n))
      (capTarget, boundaryTarget) := by
  rcases hcaps with ⟨Nc, hc⟩
  rcases hboundary with ⟨Nb, hb⟩
  refine ⟨max Nc Nb, ?_⟩
  intro n hn
  apply Prod.ext
  · exact hc n (le_trans (le_max_left _ _) hn)
  · exact hb n (le_trans (le_max_right _ _) hn)

end LongRunRSI
end DistinctionSelfReference
