import DistinctionSelfReference.GuideCore
import DistinctionSelfReference.RobustAction

namespace DistinctionSelfReference
namespace ActionFirstGuideCore

open MetaFramework

/--
Post-freeze action-first proposal. Reuse the exact same dependency vocabulary
as the frozen GuideCore, but do not rewrite its historically audited required
function or the statements imported by FreezeAudit.
-/
def required : GuideCore.Capability → Set GuideCore.Condition
  | .minimalSelfReference =>
      GuideCore.required .minimalSelfReference
  | .persistentSelf =>
      GuideCore.required .persistentSelf
  | .corrigibleSelfModel =>
      GuideCore.required .corrigibleSelfModel
  | .actor =>
      { .externalConstraint, .realityChangingAgency }
  | .finiteActor =>
      { .externalConstraint, .realityChangingAgency, .effectiveFinitude }
  | .purposefulFiniteActor =>
      { .externalConstraint, .realityChangingAgency, .effectiveFinitude,
        .purpose }
  | .localSufficiencyProblem =>
      { .externalConstraint, .realityChangingAgency, .effectiveFinitude,
        .purpose, .exploreCommitChoice }
  | .conditionalComposition =>
      GuideCore.required .conditionalComposition

/-- Revised finite graph, distinct from the frozen v1.0 GuideCore graph. -/
def graph : FrameworkGraph GuideCore.Condition GuideCore.Capability where
  derives conditions capability := required capability ⊆ conditions
  monotone := by
    intro A B capability hAB hrequired
    exact Set.Subset.trans hrequired hAB

theorem basic_action_needs_no_reflexive_prerequisite :
    GuideCore.Condition.reflexiveDistinction ∉ required .actor ∧
    GuideCore.Condition.maintainedReentry ∉ required .purposefulFiniteActor := by
  constructor <;> simp [required]

theorem frozen_actor_requires_reflexive_distinction :
    GuideCore.Condition.reflexiveDistinction ∈
      GuideCore.required .actor := by
  simp [GuideCore.required]

theorem action_requirements_subset_of_frozen :
    required .actor ⊆ GuideCore.required .actor := by
  intro c hc
  simp [required] at hc
  rcases hc with rfl | rfl <;> simp [GuideCore.required]

/--
A strict scope change, not a definitional equivalence: old v1.0 and new
actor dependence disagree on the self-reference prerequisite.
-/
theorem action_requirements_strictly_weaker_than_frozen :
    required .actor ⊂ GuideCore.required .actor := by
  rw [Set.ssubset_iff_subset_ne]
  constructor
  · exact action_requirements_subset_of_frozen
  · intro h
    have hn : GuideCore.Condition.reflexiveDistinction ∉ required .actor := by
      simp [required]
    have ho : GuideCore.Condition.reflexiveDistinction ∈
        GuideCore.required .actor := frozen_actor_requires_reflexive_distinction
    apply hn
    rw [h]
    exact ho

/--
The frozen self-reference and corrigibility branches are carried into the
new proposal *without* modification; only the action-dependency branch
is replaced.
-/
theorem preserves_frozen_reflexive_branch :
    required .minimalSelfReference = GuideCore.required .minimalSelfReference ∧
    required .persistentSelf = GuideCore.required .persistentSelf ∧
    required .corrigibleSelfModel = GuideCore.required .corrigibleSelfModel := by
  constructor
  · rfl
  constructor <;> rfl

end ActionFirstGuideCore
end DistinctionSelfReference
