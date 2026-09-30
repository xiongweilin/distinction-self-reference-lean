import DistinctionSelfReference.ArchiveRSI
import DistinctionSelfReference.EvaluatorGrounding
import DistinctionSelfReference.MorphismProvenance
import DistinctionSelfReference.CapabilityOrder

namespace DistinctionSelfReference
namespace GroundedArchiveDynamics

open ArchiveRSI
open ChangingEvaluator
open EvaluatorGrounding
open EvaluatorProvenance
open EvidenceDependency
open CapabilityOrder

universe u

/-- Every old frontier point is accepted as improved by the evaluator by some
new frontier point. -/
def EvaluatorFrontierProgress
    {Version : Type u}
    (evaluator : Evaluator Version)
    (old new : Archive Version) : Prop :=
  ∀ x, x ∈ old →
    ∃ y, y ∈ new ∧ evaluator.better x y

/-- Every old frontier point is strictly improved according to one fixed
external goal. -/
def GoalFrontierProgress
    {Version : Type u}
    (goal : Version → Nat)
    (old new : Archive Version) : Prop :=
  ∀ x, x ∈ old →
    ∃ y, y ∈ new ∧ goal x < goal y

/-- An evaluator is directly grounded in one fixed external goal. -/
def GoalSoundEvaluator
    {Version : Type u}
    (evaluator : Evaluator Version)
    (goal : Version → Nat) : Prop :=
  ∀ {a b}, evaluator.better a b → goal a < goal b

/-- A genuinely novel capability point is newly archived and is not weakly
dominated by any old archived point. -/
def HasNovelCapability
    {Version : Type u}
    [Preorder Version]
    (old new : Archive Version) : Prop :=
  ∃ y, y ∈ new ∧ y ∉ old ∧
    ∀ x, x ∈ old → ¬ y ≤ x

/-- Grounding is exactly the missing bridge from evaluator-relative frontier
progress to progress in one fixed external goal. -/
theorem goalFrontierProgress_of_evaluatorFrontierProgress
    {Version : Type u}
    (evaluator : Evaluator Version)
    (goal : Version → Nat)
    (old new : Archive Version)
    (hsound : GoalSoundEvaluator evaluator goal)
    (hprogress : EvaluatorFrontierProgress evaluator old new) :
    GoalFrontierProgress goal old new := by
  intro x hx
  rcases hprogress x hx with ⟨y, hy, hxy⟩
  exact ⟨y, hy, hsound hxy⟩

/-- Capability-order progress becomes externally grounded progress whenever the
capability order itself is sound for the fixed external goal. -/
theorem goalFrontierProgress_of_strictFrontierProgress
    {Version : Type u}
    [Preorder Version]
    (goal : Version → Nat)
    (old new : Archive Version)
    (hsound : ∀ {a b : Version}, a < b → goal a < goal b)
    (hprogress : StrictFrontierProgress old new) :
    GoalFrontierProgress goal old new := by
  intro x hx
  rcases hprogress x hx with ⟨y, hy, hxy⟩
  exact ⟨y, hy, hsound hxy⟩

namespace ArchiveGrowthWithoutFrontierChange

def before : Archive Nat := {1}

def after : Archive Nat := {0, 1}

theorem strict_archive_growth :
    StrictArchiveGrowth before after := by
  constructor
  · intro x hx
    have hx1 : x = 1 := by
      simpa [before] using hx
    subst x
    simp [after]
  · intro hback
    have h0 : 0 ∈ after := by
      simp [after]
    have := hback h0
    simp [before] at this

theorem frontier_before :
    ParetoFrontier before = ({1} : Set Nat) := by
  ext x
  simp [ParetoFrontier, before]

theorem frontier_after :
    ParetoFrontier after = ({1} : Set Nat) := by
  ext x
  simp [ParetoFrontier, after]
  omega

theorem frontier_unchanged :
    ParetoFrontier before = ParetoFrontier after := by
  rw [frontier_before, frontier_after]

theorem no_novel_capability :
    ¬ HasNovelCapability before after := by
  rintro ⟨y, hyAfter, hyNew, hnovel⟩
  have hyCases : y = 0 ∨ y = 1 := by
    simpa [after] using hyAfter
  rcases hyCases with rfl | rfl
  · exact (hnovel 1 (by simp [before])) (by omega)
  · exact hyNew (by simp [before])

/-- Strict archive cardinality/set growth can be caused entirely by a dominated
addition: neither the Pareto frontier nor the capability frontier changes. -/
theorem archive_growth_is_not_frontier_or_capability_growth :
    StrictArchiveGrowth before after ∧
    ParetoFrontier before = ParetoFrontier after ∧
    ¬ HasNovelCapability before after :=
  ⟨strict_archive_growth, frontier_unchanged, no_novel_capability⟩

end ArchiveGrowthWithoutFrontierChange

namespace CapabilityProgressWithoutEvaluatorProgress

def old : Archive Nat := {0}

def new : Archive Nat := {1}

def evaluator : Evaluator Nat where
  better _ _ := False

theorem strict_capability_frontier_progress :
    StrictFrontierProgress old new := by
  intro x hx
  have hx0 : x = 0 := by
    simpa [old] using hx
  subst x
  exact ⟨1, by simp [new], by omega⟩

theorem no_evaluator_frontier_progress :
    ¬ EvaluatorFrontierProgress evaluator old new := by
  intro h
  rcases h 0 (by simp [old]) with ⟨y, _, hy⟩
  exact hy

/-- Even genuine strict progress in the capability order need not be recognized
by an unrelated evaluator. -/
theorem capability_progress_does_not_imply_evaluator_progress :
    StrictFrontierProgress old new ∧
    ¬ EvaluatorFrontierProgress evaluator old new :=
  ⟨strict_capability_frontier_progress, no_evaluator_frontier_progress⟩

end CapabilityProgressWithoutEvaluatorProgress

namespace EvaluatorProgressWithoutGrounding

def old : Archive Bool := {false}

def new : Archive Bool := {true}

def evaluator : Evaluator Bool where
  better a b := a = false ∧ b = true

def externalGoal : Bool → Nat
  | false => 1
  | true => 0

theorem evaluator_frontier_progress :
    EvaluatorFrontierProgress evaluator old new := by
  intro x hx
  have hxFalse : x = false := by
    simpa [old] using hx
  subst x
  exact ⟨true, by simp [new], by simp [evaluator]⟩

theorem external_goal_regresses :
    externalGoal true < externalGoal false := by
  simp [externalGoal]

theorem no_goal_frontier_progress :
    ¬ GoalFrontierProgress externalGoal old new := by
  intro h
  rcases h false (by simp [old]) with ⟨y, hy, hgoal⟩
  have hyTrue : y = true := by
    simpa [new] using hy
  subst y
  simpa [externalGoal] using hgoal

theorem evaluator_not_goal_sound :
    ¬ GoalSoundEvaluator evaluator externalGoal := by
  intro h
  have hedge : evaluator.better false true := by
    simp [evaluator]
  have := h hedge
  simpa [externalGoal] using this

/-- Evaluator-relative improvement can coexist with regression of the fixed
external goal when the evaluator is not grounded. -/
theorem evaluator_progress_does_not_imply_grounded_progress :
    EvaluatorFrontierProgress evaluator old new ∧
    ¬ GoalSoundEvaluator evaluator externalGoal ∧
    ¬ GoalFrontierProgress externalGoal old new :=
  ⟨evaluator_frontier_progress, evaluator_not_goal_sound,
    no_goal_frontier_progress⟩

end EvaluatorProgressWithoutGrounding

namespace EvidenceArchiveMigration

open EvidenceDependency.SelectiveCascadeExample

abbrev E := Evidence Version Claim

def before : Archive E := {oldJudgment}

def after : Archive E := {oldJudgment, reality}

theorem historical_archive_strict_growth :
    StrictArchiveGrowth before after := by
  constructor
  · intro e he
    have heOld : e = oldJudgment := by
      simpa [before] using he
    subst e
    simp [after]
  · intro hback
    have hr : reality ∈ after := by
      simp [after]
    have hold := hback hr
    have hne : reality ≠ oldJudgment := by
      simp [reality, oldJudgment]
    exact hne (by simpa [before] using hold)

theorem retained_old_evidence_is_stale :
    oldJudgment ∈ after ∧
    ¬ CurrentEvidence preserves .current oldJudgment := by
  exact ⟨by simp [after], oldJudgment_stale⟩

theorem new_anchor_evidence_is_current :
    reality ∈ after ∧
    CurrentEvidence preserves .current reality := by
  exact ⟨by simp [after], reality_current⟩

/-- Historical archive growth is independent from migration validity: the
archive can strictly grow while retained evaluator-dependent evidence is stale
and newly added anchor evidence is current. -/
theorem archive_growth_separates_from_evidence_validity :
    StrictArchiveGrowth before after ∧
    (oldJudgment ∈ after ∧
      ¬ CurrentEvidence preserves .current oldJudgment) ∧
    (reality ∈ after ∧
      CurrentEvidence preserves .current reality) :=
  ⟨historical_archive_strict_growth,
    retained_old_evidence_is_stale,
    new_anchor_evidence_is_current⟩

end EvidenceArchiveMigration

end GroundedArchiveDynamics
end DistinctionSelfReference
