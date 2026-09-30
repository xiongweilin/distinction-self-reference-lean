import DistinctionSelfReference.EvaluatorMorphism
import DistinctionSelfReference.EvidenceDependency

namespace DistinctionSelfReference
namespace MorphismProvenance

open EvaluatorProvenance
open EvidenceDependency
open EvaluatorMorphisms
open ChangingEvaluator

universe u v

/-- The provenance policy induced by existence of an explicit version bridge. -/
def BridgePolicy
    {Version : Type u} {State : Type v}
    (evaluators : Version → Evaluator State)
    (goal : State → Nat) :
    Version → Version → Prop :=
  HasVersionBridge evaluators goal

/--
Sources covered by one old→new bridge: anchor evidence, evidence from the old
evaluator carried by the certificate, and evidence already produced by the new
evaluator.
-/
def CoveredSource
    {Version : Type u}
    (old new : Version) :
    Source Version → Prop
  | .anchor => True
  | .evaluator version => version = old ∨ version = new

theorem versionBridge_migrates_source
    {Version : Type u} {State : Type v}
    (evaluators : Version → Evaluator State)
    (goal : State → Nat)
    {old new : Version}
    (bridge : VersionBridge evaluators goal old new) :
    CurrentSource
      (BridgePolicy evaluators goal)
      new
      (.evaluator old) := by
  exact Or.inr ⟨bridge⟩

theorem coveredSource_current
    {Version : Type u} {State : Type v}
    (evaluators : Version → Evaluator State)
    (goal : State → Nat)
    {old new : Version}
    (bridge : VersionBridge evaluators goal old new)
    (source : Source Version)
    (hcovered : CoveredSource old new source) :
    CurrentSource (BridgePolicy evaluators goal) new source := by
  cases source with
  | anchor =>
      trivial
  | evaluator version =>
      rcases hcovered with hold | hnew
      · subst version
        exact versionBridge_migrates_source evaluators goal bridge
      · subst version
        exact Or.inl rfl

theorem coveredEvidence_current
    {Version : Type u} {State : Type v} {Claim : Type*}
    (evaluators : Version → Evaluator State)
    (goal : State → Nat)
    {old new : Version}
    (bridge : VersionBridge evaluators goal old new)
    (evidence : Evidence Version Claim)
    (hcovered : CoveredSource old new evidence.source) :
    CurrentEvidence
      (BridgePolicy evaluators goal)
      new
      evidence := by
  exact coveredSource_current
    evaluators goal bridge evidence.source hcovered

/--
If a bridge covers the conclusion source and every transitive dependency source,
the whole proof/evidence chain transports as current evidence.
-/
theorem bridge_transports_dependency_evidence
    {Version : Type u} {State : Type v} {Claim : Type*}
    (evaluators : Version → Evaluator State)
    (goal : State → Nat)
    {old new : Version}
    (bridge : VersionBridge evaluators goal old new)
    (dependsOn :
      Evidence Version Claim → Evidence Version Claim → Prop)
    (evidence : Evidence Version Claim)
    (hself : CoveredSource old new evidence.source)
    (hdeps :
      ∀ dependency,
        Relation.TransGen dependsOn evidence dependency →
        CoveredSource old new dependency.source) :
    DependencyCurrent
      (BridgePolicy evaluators goal)
      new
      dependsOn
      evidence := by
  constructor
  · exact coveredEvidence_current
      evaluators goal bridge evidence hself
  · intro dependency hpath
    exact coveredEvidence_current
      evaluators goal bridge dependency (hdeps dependency hpath)

/--
A concrete certificate revalidates old evaluator evidence without changing the
historical record.
-/
theorem versionBridge_revalidates_old_evidence
    {Version : Type u} {State : Type v} {Claim : Type*}
    (evaluators : Version → Evaluator State)
    (goal : State → Nat)
    {old new : Version}
    (bridge : VersionBridge evaluators goal old new)
    (evidence : Evidence Version Claim)
    (hsource : evidence.source = .evaluator old) :
    CurrentEvidence
      (BridgePolicy evaluators goal)
      new
      evidence := by
  rw [CurrentEvidence, hsource]
  exact versionBridge_migrates_source evaluators goal bridge

/--
Absent a bridge, old evaluator evidence is stale exactly as in the original
selective-erasure semantics.
-/
theorem noBridge_invalidates_old_source
    {Version : Type u} {State : Type v}
    (evaluators : Version → Evaluator State)
    (goal : State → Nat)
    {old new : Version}
    (hne : old ≠ new)
    (hnobridge : ¬ HasVersionBridge evaluators goal old new) :
    ¬ CurrentSource
      (BridgePolicy evaluators goal)
      new
      (.evaluator old) := by
  exact stale_evaluator_source_not_current
    (BridgePolicy evaluators goal) hne hnobridge

/-- Anchor evidence remains independent of all bridge choices. -/
theorem anchor_survives_without_bridge
    {Version : Type u} {State : Type v}
    (evaluators : Version → Evaluator State)
    (goal : State → Nat)
    (current : Version) :
    CurrentSource
      (BridgePolicy evaluators goal)
      current
      (.anchor : Source Version) :=
  anchor_source_always_current (BridgePolicy evaluators goal) current


namespace CompositionExample

inductive Version
  | v0
  | v1
  | v2
  deriving DecidableEq, Repr

def goal : Bool → Nat
  | false => 0
  | true => 1

def evaluators : Version → Evaluator Bool
  | .v0 => ⟨fun a b => a = false ∧ b = true⟩
  | .v1 => ⟨fun a b => (a = false ∧ b = true) ∨ a = b⟩
  | .v2 => ⟨fun _ _ => True⟩

theorem preserves01 :
    PreservesJudgments evaluators .v0 .v1 := by
  intro a b hab
  exact Or.inl hab

theorem preserves12 :
    PreservesJudgments evaluators .v1 .v2 := by
  intro _ _ _
  trivial

def bridge01 : VersionBridge evaluators goal .v0 .v1 :=
  VersionBridge.ofPreservesJudgments evaluators goal preserves01

def bridge12 : VersionBridge evaluators goal .v1 .v2 :=
  VersionBridge.ofPreservesJudgments evaluators goal preserves12

def bridge02 : VersionBridge evaluators goal .v0 .v2 :=
  VersionBridge.comp evaluators goal bridge01 bridge12

inductive Claim
  | oldJudgment
  deriving DecidableEq, Repr

def oldEvidence : Evidence Version Claim :=
  ⟨.oldJudgment, .evaluator .v0⟩

/--
Two independently certified migration steps compose into one certificate that
keeps the original evaluator evidence current at the final version.
-/
theorem composed_bridge_revalidates_original_evidence :
    CurrentEvidence
      (BridgePolicy evaluators goal)
      .v2
      oldEvidence := by
  exact versionBridge_revalidates_old_evidence
    evaluators goal bridge02 oldEvidence rfl

/-- The composed version bridge is also a genuine general evaluator morphism. -/
def composedEvaluatorMorphism :
    EvaluatorMorphism
      (evaluators .v0) (evaluators .v2) goal goal :=
  VersionBridge.toEvaluatorMorphism evaluators goal bridge02

theorem composed_morphism_preserves_improving_edge :
    (evaluators .v2).better
      (composedEvaluatorMorphism.mapState false)
      (composedEvaluatorMorphism.mapState true) := by
  exact composedEvaluatorMorphism.mapJudgment
    (by simp [evaluators])

end CompositionExample

namespace InvalidBridgeExample

open EvaluatorProvenance.GoalRelevantPreservationExample

/--
The old/current example preserves every goal-improving judgment but does not
preserve the whole evaluator relation. Therefore no full identity-state
VersionBridge certificate can exist.
-/
theorem no_full_version_bridge :
    ¬ HasVersionBridge evaluators goal .old .current := by
  rintro ⟨bridge⟩
  exact full_preservation_fails
    (VersionBridge.preservesJudgments evaluators goal bridge)

/--
This is the explicit countermodel separating a genuine full evaluator morphism
from the weaker goal-relevant edge predicate already present in PR #3.
-/
theorem goal_relevant_preservation_does_not_imply_full_morphism :
    PreservesGoalRelevantJudgments evaluators goal .old .current ∧
    ¬ HasVersionBridge evaluators goal .old .current :=
  ⟨goal_relevant_preserved, no_full_version_bridge⟩

end InvalidBridgeExample

end MorphismProvenance
end DistinctionSelfReference
