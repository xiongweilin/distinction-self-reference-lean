import DistinctionSelfReference.LocalSufficiency
import DistinctionSelfReference.ChangingEvaluator

namespace DistinctionSelfReference
namespace EvaluatorGrounding

open LocalSufficiency
open ChangingEvaluator

universe u v

/--
Evaluator soundness is semantic, not spatial: every evaluator edge must
increase the fixed external goal after that goal has been factored through
the anchor.
-/
def SoundRelativeToAnchorFactor
    {World : Type u}
    {Anchor : Type v}
    (anchor : World → Anchor)
    (goal : World → Nat)
    (evaluators : Nat → Evaluator Anchor) : Prop :=
  ∀ anchorGoal : Anchor → Nat,
    goal = anchorGoal ∘ anchor →
    ∀ n a b,
      (evaluators n).better a b →
      anchorGoal a < anchorGoal b

/--
Baseline grounded-improvement theorem.

If the anchor is sufficient for the external goal, evaluator judgments are
sound for every valid anchor factorization of that goal, and every local step
is evaluator-improving, then every finite nonempty trajectory prefix strictly
improves the same fixed external goal.
-/
theorem grounded_local_improvement_implies_global_goal_improvement
    {World : Type u}
    {Anchor : Type v}
    (anchor : World → Anchor)
    (goal : World → Nat)
    (evaluators : Nat → Evaluator Anchor)
    (trajectory : Nat → World)
    (hsufficient : Sufficient anchor goal)
    (hsound : SoundRelativeToAnchorFactor anchor goal evaluators)
    (hlocal :
      LocalImprovement evaluators (fun n => anchor (trajectory n))) :
    ∀ n, goal (trajectory 0) < goal (trajectory (n + 1)) := by
  rcases hsufficient with ⟨anchorGoal, hfactor⟩
  have hs :
      ∀ n a b,
        (evaluators n).better a b →
        anchorGoal a < anchorGoal b :=
    hsound anchorGoal hfactor
  have hstep :
      ∀ n, goal (trajectory n) < goal (trajectory (n + 1)) := by
    intro n
    rw [hfactor]
    exact hs n _ _ (hlocal n)
  intro n
  induction n with
  | zero =>
      exact hstep 0
  | succ n ih =>
      exact lt_trans ih (hstep (n + 1))

/--
Goal-grounding form of the LocalSufficiency theorem:
the anchor is sufficient exactly when no anchor-indistinguishable worlds demand
different goal-relevant judgments.
-/
theorem anchor_sufficient_iff_no_goal_ambiguity
    {World : Type u}
    {Anchor : Type v}
    {Judgment : Type*}
    [Nonempty Judgment]
    {anchor : World → Anchor}
    {required : World → Judgment} :
    Sufficient anchor required ↔ ¬ Ambiguous anchor required :=
  sufficient_iff_not_ambiguous

namespace ProxyDriftExample

abbrev World := Bool × Bool

/-- The actor sees only the first bit. -/
def anchor : World → Bool :=
  Prod.fst

/-- The external goal depends only on the hidden second bit. -/
def externalGoal : World → Nat
  | (_, false) => 0
  | (_, true) => 1

/-- A coarse anchor-level score used by the validator. -/
def anchorScore : Bool → Nat
  | false => 0
  | true => 1

def evaluator₀ : Evaluator Bool where
  better a b := a = b

def evaluator₁ : Evaluator Bool where
  better a b := a = b ∨ (a = false ∧ b = true)

def evaluators : Nat → Evaluator Bool
  | 0 => evaluator₀
  | _ + 1 => evaluator₁

/--
Anchor validation checks only that evaluator-approved moves do not reduce the
coarse anchor score.
-/
def AnchorValidated (evaluator : Evaluator Bool) : Prop :=
  ∀ a b, evaluator.better a b → anchorScore a ≤ anchorScore b

theorem evaluator₀_validated :
    AnchorValidated evaluator₀ := by
  intro a b hab
  exact le_of_eq (congrArg anchorScore hab)

theorem evaluator₁_validated :
    AnchorValidated evaluator₁ := by
  intro a b hab
  rcases hab with hab | ⟨ha, hb⟩
  · exact le_of_eq (congrArg anchorScore hab)
  · subst a
    subst b
    simp [anchorScore]

theorem every_evaluator_validated :
    ∀ n, AnchorValidated (evaluators n) := by
  intro n
  cases n with
  | zero =>
      exact evaluator₀_validated
  | succ n =>
      exact evaluator₁_validated

/--
The evaluator really changes: version 1 accepts an anchor move that version 0
does not.
-/
theorem evaluator_migration_changes_judgment :
    ¬ evaluator₀.better false true ∧
      evaluator₁.better false true := by
  constructor <;> simp [evaluator₀, evaluator₁]

/--
The visible anchor never changes. Reality first regresses on the hidden goal
and then stays there.
-/
def trajectory : Nat → World
  | 0 => (false, true)
  | _ + 1 => (false, false)

theorem local_improvement_every_step :
    LocalImprovement evaluators (fun n => anchor (trajectory n)) := by
  intro n
  cases n with
  | zero =>
      simp [evaluators, evaluator₀, trajectory, anchor]
  | succ n =>
      simp [evaluators, evaluator₁, trajectory, anchor]

theorem anchor_ambiguous_for_external_goal :
    Ambiguous anchor externalGoal := by
  refine ⟨(false, true), (false, false), rfl, ?_⟩
  simp [externalGoal]

theorem anchor_insufficient_for_external_goal :
    ¬ Sufficient anchor externalGoal :=
  ambiguous_not_sufficient anchor_ambiguous_for_external_goal

theorem external_goal_regresses_on_first_step :
    externalGoal (trajectory 1) < externalGoal (trajectory 0) := by
  simp [trajectory, externalGoal]

/--
Sharp proxy-drift counterexample.

A finite external signal exists, evaluator migration occurs, every evaluator
passes anchor-only validation, and every step is locally evaluator-improving;
nevertheless the true external goal regresses because the anchor is
insufficient for that goal.
-/
theorem validated_anchor_signal_does_not_prevent_proxy_regression :
    (∀ n, AnchorValidated (evaluators n)) ∧
    LocalImprovement evaluators (fun n => anchor (trajectory n)) ∧
    (¬ Sufficient anchor externalGoal) ∧
    externalGoal (trajectory 1) < externalGoal (trajectory 0) := by
  exact ⟨
    every_evaluator_validated,
    local_improvement_every_step,
    anchor_insufficient_for_external_goal,
    external_goal_regresses_on_first_step⟩

/--
A long-run hidden proxy cycle: the finite visible anchor remains constantly
false while the hidden external goal alternates forever.
-/
def cyclingTrajectory : Nat → World :=
  fun n => (false, n % 2 = 0)

theorem cycling_anchor_constant :
    ∀ n, anchor (cyclingTrajectory n) = false := by
  intro n
  rfl

theorem cycling_local_improvement_every_step :
    LocalImprovement evaluators
      (fun n => anchor (cyclingTrajectory n)) := by
  intro n
  change (evaluators n).better
    (anchor (cyclingTrajectory n))
    (anchor (cyclingTrajectory (n + 1)))
  rw [cycling_anchor_constant n, cycling_anchor_constant (n + 1)]
  cases n with
  | zero =>
      simp [evaluators, evaluator₀]
  | succ n =>
      simp [evaluators, evaluator₁]

theorem cycling_goal_alternates :
    ∀ k,
      externalGoal (cyclingTrajectory (2 * k)) = 1 ∧
      externalGoal (cyclingTrajectory (2 * k + 1)) = 0 := by
  intro k
  constructor
  · simp [cyclingTrajectory, externalGoal]
  · simp [cyclingTrajectory, externalGoal]

theorem cycling_has_infinitely_many_regressions :
    ∀ k,
      externalGoal (cyclingTrajectory (2 * k + 1)) <
        externalGoal (cyclingTrajectory (2 * k)) := by
  intro k
  rw [(cycling_goal_alternates k).1, (cycling_goal_alternates k).2]
  decide

/--
Finite anchor validation can therefore coexist not merely with one mistaken
step but with unboundedly many true-goal regressions.
-/
theorem validated_finite_anchor_allows_perpetual_proxy_cycle :
    (∀ n, AnchorValidated (evaluators n)) ∧
    LocalImprovement evaluators
      (fun n => anchor (cyclingTrajectory n)) ∧
    (¬ Sufficient anchor externalGoal) ∧
    (∀ k,
      externalGoal (cyclingTrajectory (2 * k + 1)) <
        externalGoal (cyclingTrajectory (2 * k))) := by
  exact ⟨
    every_evaluator_validated,
    cycling_local_improvement_every_step,
    anchor_insufficient_for_external_goal,
    cycling_has_infinitely_many_regressions⟩

end ProxyDriftExample

end EvaluatorGrounding
end DistinctionSelfReference
