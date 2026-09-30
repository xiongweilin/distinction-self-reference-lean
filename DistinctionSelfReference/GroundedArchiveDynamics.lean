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
open MorphismProvenance
open EvaluatorMorphisms

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

/-- An evaluator is capability-sound when every accepted improvement edge
is a strict edge of the capability preorder. -/
def CapabilitySoundEvaluator
    {Version : Type u}
    [Preorder Version]
    (evaluator : Evaluator Version) : Prop :=
  ∀ {a b}, evaluator.better a b → a < b

/-- Capability-sound evaluator progress is genuine strict frontier progress. -/
theorem strictFrontierProgress_of_evaluatorFrontierProgress
    {Version : Type u}
    [Preorder Version]
    (evaluator : Evaluator Version)
    (old new : Archive Version)
    (hsound : CapabilitySoundEvaluator evaluator)
    (hprogress : EvaluatorFrontierProgress evaluator old new) :
    StrictFrontierProgress old new := by
  intro x hx
  rcases hprogress x hx with ⟨y, hy, hxy⟩
  exact ⟨y, hy, hsound hxy⟩

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

/-- Map an archive along an explicit state translation. -/
def mapArchive
    {Source Target : Type*}
    (f : Source → Target)
    (archive : Archive Source) :
    Archive Target :=
  f '' archive

/-- A general evaluator morphism transports evaluator-relative frontier
progress to the image frontiers. -/
theorem evaluatorFrontierProgress_map_morphism
    {Source Target : Type*}
    {source : Evaluator Source}
    {target : Evaluator Target}
    {sourceGoal : Source → Nat}
    {targetGoal : Target → Nat}
    (m :
      EvaluatorMorphism source target sourceGoal targetGoal)
    (old new : Archive Source)
    (hprogress :
      EvaluatorFrontierProgress source old new) :
    EvaluatorFrontierProgress target
      (mapArchive m.mapState old)
      (mapArchive m.mapState new) := by
  intro x hx
  rcases hx with ⟨a, ha, rfl⟩
  rcases hprogress a ha with ⟨b, hb, hab⟩
  exact ⟨m.mapState b, ⟨b, hb, rfl⟩,
    m.mapJudgment hab⟩

/-- Because evaluator morphisms also preserve the fixed external goal, they
transport grounded goal progress to image frontiers as well. -/
theorem goalFrontierProgress_map_morphism
    {Source Target : Type*}
    {source : Evaluator Source}
    {target : Evaluator Target}
    {sourceGoal : Source → Nat}
    {targetGoal : Target → Nat}
    (m :
      EvaluatorMorphism source target sourceGoal targetGoal)
    (old new : Archive Source)
    (hprogress :
      GoalFrontierProgress sourceGoal old new) :
    GoalFrontierProgress targetGoal
      (mapArchive m.mapState old)
      (mapArchive m.mapState new) := by
  intro x hx
  rcases hx with ⟨a, ha, rfl⟩
  rcases hprogress a ha with ⟨b, hb, hab⟩
  refine ⟨m.mapState b, ⟨b, hb, rfl⟩, ?_⟩
  rw [m.mapGoal a, m.mapGoal b]
  exact hab

/-- Same-state evaluator migration preserves a certified frontier-improvement
claim directly. -/
theorem evaluatorFrontierProgress_transport_versionBridge
    {Version State : Type*}
    (evaluators : Version → Evaluator State)
    (goal : State → Nat)
    {oldVersion newVersion : Version}
    (bridge :
      VersionBridge evaluators goal oldVersion newVersion)
    (oldFrontier newFrontier : Archive State)
    (hprogress :
      EvaluatorFrontierProgress
        (evaluators oldVersion)
        oldFrontier newFrontier) :
    EvaluatorFrontierProgress
      (evaluators newVersion)
      oldFrontier newFrontier := by
  intro x hx
  rcases hprogress x hx with ⟨y, hy, hxy⟩
  exact ⟨y, hy,
    bridge.certificate.preservesJudgment hxy⟩

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

/--
If the capability order itself has no infinite strict ascending chain, then a
sequence of nonempty-start frontiers cannot be evaluator-improving at every
step when every evaluator version is capability-sound.
-/
theorem wellFoundedGT_forbids_perpetual_capabilitySoundEvaluatorProgress
    {Version : Type u}
    [Preorder Version]
    [WellFoundedGT Version]
    (evaluators : Nat → Evaluator Version)
    (frontier : Nat → Archive Version)
    (h0 : (frontier 0).Nonempty)
    (hsound :
      ∀ n, CapabilitySoundEvaluator (evaluators n))
    (hprogress :
      ∀ n,
        EvaluatorFrontierProgress (evaluators n)
          (frontier n) (frontier (n + 1))) :
    False := by
  apply
    wellFoundedGT_forbids_perpetual_strict_frontier_progress
      frontier h0
  intro n
  exact strictFrontierProgress_of_evaluatorFrontierProgress
    (evaluators n) (frontier n) (frontier (n + 1))
    (hsound n) (hprogress n)

/--
A fixed bounded external objective forbids strict grounded frontier progress at
every step forever.

This is deliberately stronger and more relevant to grounded archive dynamics
than bare WQO: the obstruction comes from the fixed external objective itself.
-/
theorem boundedGoal_forbids_perpetual_goalFrontierProgress
    {Version : Type u}
    (goal : Version → Nat)
    (frontier : Nat → Archive Version)
    (B : Nat)
    (h0 : (frontier 0).Nonempty)
    (hbound :
      ∀ n x, x ∈ frontier n → goal x ≤ B)
    (hprogress :
      ∀ n,
        GoalFrontierProgress goal
          (frontier n) (frontier (n + 1))) :
    False := by
  classical
  let first : {x // x ∈ frontier 0} :=
    ⟨h0.choose, h0.choose_spec⟩
  let next :
      ∀ n, {x // x ∈ frontier n} →
        {y // y ∈ frontier (n + 1)} :=
    fun n x =>
      ⟨(hprogress n x.1 x.2).choose,
        (hprogress n x.1 x.2).choose_spec.1⟩
  let seq : ∀ n, {x // x ∈ frontier n} :=
    fun n => Nat.rec first (fun n x => next n x) n
  have hseq_succ :
      ∀ n, seq (n + 1) = next n (seq n) := by
    intro n
    rfl
  have hstep :
      ∀ n, goal (seq n).1 < goal (seq (n + 1)).1 := by
    intro n
    rw [hseq_succ n]
    simpa [next] using
      (hprogress n (seq n).1 (seq n).2).choose_spec.2
  have hstrict : StrictMono (fun n => goal (seq n).1) :=
    strictMono_nat_of_lt_succ hstep
  have hlower : B + 1 ≤ goal (seq (B + 1)).1 :=
    hstrict.id_le (B + 1)
  have hupper : goal (seq (B + 1)).1 ≤ B :=
    hbound (B + 1) (seq (B + 1)).1 (seq (B + 1)).2
  omega

/--
The same stopping criterion applies to evaluator-relative frontier progress once
every evaluator version is grounded in the same bounded external goal.
-/
theorem boundedGoal_forbids_perpetual_groundedEvaluatorProgress
    {Version : Type u}
    (evaluators : Nat → Evaluator Version)
    (goal : Version → Nat)
    (frontier : Nat → Archive Version)
    (B : Nat)
    (h0 : (frontier 0).Nonempty)
    (hbound :
      ∀ n x, x ∈ frontier n → goal x ≤ B)
    (hsound :
      ∀ n, GoalSoundEvaluator (evaluators n) goal)
    (hprogress :
      ∀ n,
        EvaluatorFrontierProgress (evaluators n)
          (frontier n) (frontier (n + 1))) :
    False := by
  apply boundedGoal_forbids_perpetual_goalFrontierProgress
    goal frontier B h0 hbound
  intro n
  exact goalFrontierProgress_of_evaluatorFrontierProgress
    (evaluators n) goal (frontier n) (frontier (n + 1))
    (hsound n) (hprogress n)

/--
An explicit version bridge transports an entire historical evidence archive
into the dependency-current view when it covers every record and every
transitive dependency of every record.
-/
theorem coveredEvidenceArchive_transports_under_bridge
    {Version : Type u} {State Claim : Type*}
    (evaluators : Version → Evaluator State)
    (goal : State → Nat)
    {old new : Version}
    (bridge : VersionBridge evaluators goal old new)
    (dependsOn :
      Evidence Version Claim → Evidence Version Claim → Prop)
    (history : Archive (Evidence Version Claim))
    (hself :
      ∀ e, e ∈ history →
        CoveredSource old new e.source)
    (hdeps :
      ∀ e, e ∈ history →
        ∀ dependency,
          Relation.TransGen dependsOn e dependency →
          CoveredSource old new dependency.source) :
    history ⊆
      DependencyCurrentHistory
        (BridgePolicy evaluators goal)
        new dependsOn history := by
  intro e he
  exact ⟨he,
    bridge_transports_dependency_evidence
      evaluators goal bridge dependsOn e
      (hself e he) (hdeps e he)⟩

/--
If a retained historical archive contains unsupported evidence from an old
evaluator version, then that whole archive cannot be treated as current after
migration merely because it was retained.
-/
theorem retainedArchive_not_all_current_without_bridge
    {Version : Type u} {State Claim : Type*}
    (evaluators : Version → Evaluator State)
    (goal : State → Nat)
    {old new : Version}
    (hne : old ≠ new)
    (hnobridge :
      ¬ HasVersionBridge evaluators goal old new)
    (history : Archive (Evidence Version Claim))
    (e : Evidence Version Claim)
    (he : e ∈ history)
    (hsource : e.source = .evaluator old) :
    ¬ history ⊆
      CurrentHistory
        (BridgePolicy evaluators goal)
        new history := by
  intro hall
  have hcurrent := (hall he).2
  rw [CurrentEvidence, hsource] at hcurrent
  exact
    (noBridge_invalidates_old_source
      evaluators goal hne hnobridge) hcurrent

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

/--
Strict progress from a nonempty Pareto-style frontier forces genuine capability
novelty once the old frontier is both an antichain and dominance-complete for
the old archive.

This is the bridge from "frontier replacement" to "new capability" that is
missing from archive cardinality growth alone.
-/
theorem novelCapability_of_strictFrontierProgress
    {Version : Type u}
    [Preorder Version]
    (oldArchive oldFrontier newFrontier : Archive Version)
    (h0 : oldFrontier.Nonempty)
    (hanti : IsAntichain (· ≤ ·) oldFrontier)
    (hcomplete :
      DominanceComplete oldFrontier oldArchive)
    (hprogress :
      StrictFrontierProgress oldFrontier newFrontier) :
    HasNovelCapability oldArchive newFrontier := by
  rcases h0 with ⟨x, hx⟩
  rcases hprogress x hx with ⟨y, hyNew, hxy⟩
  have hnotDominated :
      ∀ z, z ∈ oldArchive → ¬ y ≤ z := by
    intro z hz hyz
    rcases hcomplete.2 z hz with ⟨f, hf, hzf⟩
    have hyf : y ≤ f := le_trans hyz hzf
    have hxf : x < f := lt_of_lt_of_le hxy hyf
    have hne : x ≠ f := ne_of_lt hxf
    exact hne (hanti.eq hx hf (le_of_lt hxf))
  have hyOld : y ∉ oldArchive := by
    intro hy
    exact (hnotDominated y hy) le_rfl
  exact ⟨y, hyNew, hyOld, hnotDominated⟩

namespace FrontierReplacementWithoutNovelty

def old : Archive Nat := {1}

def new : Archive Nat := {0}

theorem frontier_replaced :
    old ≠ new := by
  intro h
  have h1 : 1 ∈ old := by simp [old]
  have := h ▸ h1
  simp [new] at this

theorem no_novel_capability :
    ¬ HasNovelCapability old new := by
  rintro ⟨y, hyNew, _, hnovel⟩
  have hy0 : y = 0 := by
    simpa [new] using hyNew
  subst y
  exact (hnovel 1 (by simp [old])) (by omega)

/-- Merely replacing the frontier set says nothing about improvement direction:
a replacement can move strictly downward in the capability order. -/
theorem frontier_replacement_does_not_imply_novelty :
    old ≠ new ∧ ¬ HasNovelCapability old new :=
  ⟨frontier_replaced, no_novel_capability⟩

end FrontierReplacementWithoutNovelty

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
  constructor
  · intro hx
    simpa [before] using hx.1
  · intro hx
    have hx1 : x = 1 := by
      simpa using hx
    subst x
    constructor
    · simp [before]
    · intro y hy
      have hy1 : y = 1 := by
        simpa [before] using hy
      subst y
      exact lt_irrefl 1

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

namespace GoalProgressWithoutCapabilityNovelty

def old : Archive Nat := {1}

def new : Archive Nat := {0}

def externalGoal : Nat → Nat
  | 0 => 1
  | _ => 0

theorem grounded_goal_progress :
    GoalFrontierProgress externalGoal old new := by
  intro x hx
  have hx1 : x = 1 := by
    simpa [old] using hx
  subst x
  exact ⟨0, by simp [new], by simp [externalGoal]⟩

theorem no_novel_capability :
    ¬ HasNovelCapability old new := by
  rintro ⟨y, hyNew, _, hnovel⟩
  have hy0 : y = 0 := by
    simpa [new] using hyNew
  subst y
  exact (hnovel 1 (by simp [old])) (by omega)

/--
Progress in one externally fixed objective need not add a capability in an
independent capability preorder. Grounded goal progress is therefore still
task/objective relative.
-/
theorem grounded_progress_does_not_imply_capability_novelty :
    GoalFrontierProgress externalGoal old new ∧
    ¬ HasNovelCapability old new :=
  ⟨grounded_goal_progress, no_novel_capability⟩

end GoalProgressWithoutCapabilityNovelty

namespace CapabilityNoveltyWithoutGoalProgress

def old : Archive Nat := {0}

def new : Archive Nat := {1}

def externalGoal (_ : Nat) : Nat := 0

theorem novel_capability :
    HasNovelCapability old new := by
  refine ⟨1, by simp [new], by simp [old], ?_⟩
  intro x hx hle
  have hx0 : x = 0 := by
    simpa [old] using hx
  subst x
  omega

theorem no_grounded_goal_progress :
    ¬ GoalFrontierProgress externalGoal old new := by
  intro h
  rcases h 0 (by simp [old]) with ⟨y, _, hy⟩
  simp [externalGoal] at hy

/--
A genuinely new capability can be irrelevant to the chosen external objective.
Capability novelty therefore does not imply grounded progress for an arbitrary
fixed goal.
-/
theorem capability_novelty_does_not_imply_grounded_progress :
    HasNovelCapability old new ∧
    ¬ GoalFrontierProgress externalGoal old new :=
  ⟨novel_capability, no_grounded_goal_progress⟩

end CapabilityNoveltyWithoutGoalProgress

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
