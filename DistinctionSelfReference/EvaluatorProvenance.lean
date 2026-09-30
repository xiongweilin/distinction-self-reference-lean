import DistinctionSelfReference.ChangingEvaluator

namespace DistinctionSelfReference
namespace EvaluatorProvenance

open ChangingEvaluator

universe u v w

/-- Evidence is either evaluator-independent anchor/reality evidence or tied to
one evaluator version. -/
inductive Source (Version : Type u)
  | anchor
  | evaluator (version : Version)
  deriving DecidableEq, Repr

structure Evidence (Version : Type u) (Claim : Type v) where
  claim : Claim
  source : Source Version
  deriving DecidableEq, Repr

/--
A preservation relation determines which old evaluator-dependent judgments may
remain current after migration.
-/
def CurrentSource
    {Version : Type u}
    (preserves : Version → Version → Prop)
    (current : Version) :
    Source Version → Prop
  | .anchor => True
  | .evaluator old =>
      old = current ∨ preserves old current

def CurrentEvidence
    {Version : Type u}
    {Claim : Type v}
    (preserves : Version → Version → Prop)
    (current : Version)
    (evidence : Evidence Version Claim) : Prop :=
  CurrentSource preserves current evidence.source

/--
History is retained independently from whether a record is still admissible as
current evidence.
-/
def CurrentHistory
    {Version : Type u}
    {Claim : Type v}
    (preserves : Version → Version → Prop)
    (current : Version)
    (history : Set (Evidence Version Claim)) :
    Set (Evidence Version Claim) :=
  {e | e ∈ history ∧ CurrentEvidence preserves current e}

theorem currentHistory_subset_history
    {Version : Type u}
    {Claim : Type v}
    (preserves : Version → Version → Prop)
    (current : Version)
    (history : Set (Evidence Version Claim)) :
    CurrentHistory preserves current history ⊆ history := by
  intro e he
  exact he.1

/-- Evaluator-independent anchor evidence survives every migration. -/
theorem anchor_source_always_current
    {Version : Type u}
    (preserves : Version → Version → Prop)
    (current : Version) :
    CurrentSource preserves current (.anchor : Source Version) := by
  trivial

/-- Evidence from the current evaluator is current without an extra migration
proof. -/
theorem current_evaluator_source_is_current
    {Version : Type u}
    (preserves : Version → Version → Prop)
    (current : Version) :
    CurrentSource preserves current (.evaluator current) := by
  exact Or.inl rfl

/-- A proved preservation/refinement edge lets old evaluator-dependent evidence
migrate to the new evaluator. -/
theorem preserved_evaluator_source_migrates
    {Version : Type u}
    (preserves : Version → Version → Prop)
    {old current : Version}
    (hpreserves : preserves old current) :
    CurrentSource preserves current (.evaluator old) := by
  exact Or.inr hpreserves

/-- Without equality or a preservation edge, old evaluator-dependent evidence
loses current qualification. -/
theorem stale_evaluator_source_not_current
    {Version : Type u}
    (preserves : Version → Version → Prop)
    {old current : Version}
    (hne : old ≠ current)
    (hnop : ¬ preserves old current) :
    ¬ CurrentSource preserves current (.evaluator old) := by
  intro h
  rcases h with heq | hpres
  · exact hne heq
  · exact hnop hpres

/--
Selective erasure theorem: migration does not erase history, but it removes
current qualification from unsupported evaluator-dependent evidence while
retaining anchor evidence.
-/
theorem migration_selectively_invalidates
    {Version : Type u}
    (preserves : Version → Version → Prop)
    {old current : Version}
    (hne : old ≠ current)
    (hnop : ¬ preserves old current) :
    CurrentSource preserves old (.anchor : Source Version) ∧
    CurrentSource preserves old (.evaluator old) ∧
    CurrentSource preserves current (.anchor : Source Version) ∧
    ¬ CurrentSource preserves current (.evaluator old) := by
  exact ⟨
    anchor_source_always_current preserves old,
    current_evaluator_source_is_current preserves old,
    anchor_source_always_current preserves current,
    stale_evaluator_source_not_current preserves hne hnop⟩

/-- Concrete semantic preservation between evaluator versions: every old
judgment is still accepted by the new evaluator. -/
def PreservesJudgments
    {Version : Type u}
    {State : Type v}
    (evaluators : Version → Evaluator State)
    (old new : Version) : Prop :=
  ∀ a b,
    (evaluators old).better a b →
    (evaluators new).better a b

theorem preservesJudgments_refl
    {Version : Type u}
    {State : Type v}
    (evaluators : Version → Evaluator State)
    (version : Version) :
    PreservesJudgments evaluators version version := by
  intro a b hab
  exact hab

theorem preservesJudgments_trans
    {Version : Type u}
    {State : Type v}
    (evaluators : Version → Evaluator State)
    {v₀ v₁ v₂ : Version}
    (h₀₁ : PreservesJudgments evaluators v₀ v₁)
    (h₁₂ : PreservesJudgments evaluators v₁ v₂) :
    PreservesJudgments evaluators v₀ v₂ := by
  intro a b hab
  exact h₁₂ a b (h₀₁ a b hab)

theorem judgment_refinement_migrates_source
    {Version : Type u}
    {State : Type v}
    (evaluators : Version → Evaluator State)
    {old current : Version}
    (hrefine : PreservesJudgments evaluators old current) :
    CurrentSource
      (PreservesJudgments evaluators)
      current
      (.evaluator old) := by
  exact Or.inr hrefine

/--
Weaker migration criterion: preserve only those old evaluator judgments that
are semantically relevant to a fixed external goal.
-/
def PreservesGoalRelevantJudgments
    {Version : Type u}
    {State : Type v}
    (evaluators : Version → Evaluator State)
    (goal : State → Nat)
    (old new : Version) : Prop :=
  ∀ a b,
    (evaluators old).better a b →
    goal a < goal b →
    (evaluators new).better a b

theorem preservesGoalRelevantJudgments_refl
    {Version : Type u}
    {State : Type v}
    (evaluators : Version → Evaluator State)
    (goal : State → Nat)
    (version : Version) :
    PreservesGoalRelevantJudgments evaluators goal version version := by
  intro a b hab _
  exact hab

theorem preservesGoalRelevantJudgments_trans
    {Version : Type u}
    {State : Type v}
    (evaluators : Version → Evaluator State)
    (goal : State → Nat)
    {v₀ v₁ v₂ : Version}
    (h₀₁ : PreservesGoalRelevantJudgments evaluators goal v₀ v₁)
    (h₁₂ : PreservesGoalRelevantJudgments evaluators goal v₁ v₂) :
    PreservesGoalRelevantJudgments evaluators goal v₀ v₂ := by
  intro a b hab hgoal
  exact h₁₂ a b (h₀₁ a b hab hgoal) hgoal

theorem full_preservation_implies_goal_relevant_preservation
    {Version : Type u}
    {State : Type v}
    (evaluators : Version → Evaluator State)
    (goal : State → Nat)
    {old new : Version}
    (hfull : PreservesJudgments evaluators old new) :
    PreservesGoalRelevantJudgments evaluators goal old new := by
  intro a b hab _
  exact hfull a b hab

theorem goal_relevant_refinement_migrates_source
    {Version : Type u}
    {State : Type v}
    (evaluators : Version → Evaluator State)
    (goal : State → Nat)
    {old current : Version}
    (hrefine :
      PreservesGoalRelevantJudgments evaluators goal old current) :
    CurrentSource
      (PreservesGoalRelevantJudgments evaluators goal)
      current
      (.evaluator old) := by
  exact Or.inr hrefine

namespace GoalRelevantPreservationExample

inductive Version
  | old
  | current
  deriving DecidableEq, Repr

def goal : Bool → Nat
  | false => 0
  | true => 1

/--
The old evaluator accepts both directions; the current evaluator drops the
goal-regressing direction and retains only the goal-improving one.
-/
def evaluators : Version → Evaluator Bool
  | .old =>
      ⟨fun a b => a ≠ b⟩
  | .current =>
      ⟨fun a b => a = false ∧ b = true⟩

theorem goal_relevant_preserved :
    PreservesGoalRelevantJudgments evaluators goal .old .current := by
  intro a b hab hgoal
  cases a <;> cases b <;> simp [goal, evaluators] at hab hgoal ⊢

theorem full_preservation_fails :
    ¬ PreservesJudgments evaluators .old .current := by
  intro h
  have hold : (evaluators .old).better true false := by
    simp [evaluators]
  have hnew := h true false hold
  simpa [evaluators] using hnew

/--
Goal-relevant preservation is strictly weaker than preserving the evaluator's
entire old judgment relation.
-/
theorem goal_relevant_preservation_strictly_weaker :
    PreservesGoalRelevantJudgments evaluators goal .old .current ∧
    ¬ PreservesJudgments evaluators .old .current :=
  ⟨goal_relevant_preserved, full_preservation_fails⟩

end GoalRelevantPreservationExample

/--
The claim payload itself is not rewritten by evaluator migration. Only the
qualification predicate changes.
-/
theorem migration_preserves_historical_claim
    {Version : Type u}
    {Claim : Type v}
    (e : Evidence Version Claim)
    (old current : Version) :
    e.claim = e.claim := by
  rfl

/--
An anchor record already present in history remains in every current view.
-/
theorem anchor_evidence_retained
    {Version : Type u}
    {Claim : Type v}
    (preserves : Version → Version → Prop)
    (current : Version)
    (history : Set (Evidence Version Claim))
    (e : Evidence Version Claim)
    (hmem : e ∈ history)
    (hanchor : e.source = .anchor) :
    e ∈ CurrentHistory preserves current history := by
  constructor
  · exact hmem
  · rw [CurrentEvidence, hanchor]
    trivial

/--
Unsupported old evaluator evidence remains historical but is absent from the
new current-evidence view.
-/
theorem stale_evidence_retained_but_not_current
    {Version : Type u}
    {Claim : Type v}
    (preserves : Version → Version → Prop)
    {old current : Version}
    (hne : old ≠ current)
    (hnop : ¬ preserves old current)
    (history : Set (Evidence Version Claim))
    (e : Evidence Version Claim)
    (hmem : e ∈ history)
    (hsource : e.source = .evaluator old) :
    e ∈ history ∧
      e ∉ CurrentHistory preserves current history := by
  constructor
  · exact hmem
  · intro hcurrent
    have hqual := hcurrent.2
    rw [CurrentEvidence, hsource] at hqual
    exact stale_evaluator_source_not_current preserves hne hnop hqual

end EvaluatorProvenance
end DistinctionSelfReference
