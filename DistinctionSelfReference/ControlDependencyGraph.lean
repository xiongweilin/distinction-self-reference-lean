import DistinctionSelfReference.MetaFramework
import DistinctionSelfReference.ControlAblation

namespace DistinctionSelfReference
namespace ControlDependencyGraph

open MetaFramework

/-- Conditions isolated by the control-simulation ablation experiments. -/
inductive Condition
  | forwardSimulation
  | safetyPreservation
  | backwardSimulation
  | safetyReflection
  deriving DecidableEq, Repr

/-- Capability directions already formalized for viability and recovery. -/
inductive Capability
  | preserveViability
  | preserveRecovery
  | reflectViability
  | reflectRecovery
  deriving DecidableEq, Repr

/-- The exact condition profile validated by the current theorem/countermodel layer. -/
def required : Capability → Set Condition
  | .preserveViability => { .forwardSimulation, .safetyPreservation }
  | .preserveRecovery => { .forwardSimulation, .safetyPreservation }
  | .reflectViability => { .backwardSimulation, .safetyReflection }
  | .reflectRecovery => { .backwardSimulation, .safetyReflection }

/--
The concrete dependency graph: a capability is available exactly when all
conditions isolated as necessary by the current ablation models are present.
-/
def graph : FrameworkGraph Condition Capability where
  derives S cap := required cap ⊆ S
  monotone := by
    intro A B cap hAB hreq
    exact Set.Subset.trans hreq hAB

theorem forwardPair_minimal_for_viability :
    graph.InclusionMinimal
      {Condition.forwardSimulation, Condition.safetyPreservation}
      {Capability.preserveViability} := by
  rw [← graph.ablationMinimal_iff_inclusionMinimal]
  constructor
  · intro cap hcap
    change required cap ⊆
      {Condition.forwardSimulation, Condition.safetyPreservation}
    change cap = Capability.preserveViability at hcap
    subst cap
    intro c hc
    exact hc
  · intro c hc hafter
    have hreq := hafter (t := Capability.preserveViability) (by rfl)
    change required Capability.preserveViability ⊆
      ({Condition.forwardSimulation, Condition.safetyPreservation} \ {c}) at hreq
    have hcReq : c ∈ required Capability.preserveViability := by
      change c ∈ ({Condition.forwardSimulation, Condition.safetyPreservation} : Set Condition)
      exact hc
    have hcDiff := hreq hcReq
    exact hcDiff.2 (by
      change c = c
      rfl)

theorem forwardPair_minimal_for_recovery :
    graph.InclusionMinimal
      {Condition.forwardSimulation, Condition.safetyPreservation}
      {Capability.preserveRecovery} := by
  rw [← graph.ablationMinimal_iff_inclusionMinimal]
  constructor
  · intro cap hcap
    change cap = Capability.preserveRecovery at hcap
    subst cap
    intro c hc
    exact hc
  · intro c hc hafter
    have hreq := hafter (t := Capability.preserveRecovery) (by rfl)
    have hcReq : c ∈ required Capability.preserveRecovery := by
      change c ∈ ({Condition.forwardSimulation, Condition.safetyPreservation} : Set Condition)
      exact hc
    have hcDiff := hreq hcReq
    exact hcDiff.2 (by change c = c; rfl)

theorem backwardPair_minimal_for_viability :
    graph.InclusionMinimal
      {Condition.backwardSimulation, Condition.safetyReflection}
      {Capability.reflectViability} := by
  rw [← graph.ablationMinimal_iff_inclusionMinimal]
  constructor
  · intro cap hcap
    change cap = Capability.reflectViability at hcap
    subst cap
    intro c hc
    exact hc
  · intro c hc hafter
    have hreq := hafter (t := Capability.reflectViability) (by rfl)
    have hcReq : c ∈ required Capability.reflectViability := by
      change c ∈ ({Condition.backwardSimulation, Condition.safetyReflection} : Set Condition)
      exact hc
    have hcDiff := hreq hcReq
    exact hcDiff.2 (by change c = c; rfl)

theorem backwardPair_minimal_for_recovery :
    graph.InclusionMinimal
      {Condition.backwardSimulation, Condition.safetyReflection}
      {Capability.reflectRecovery} := by
  rw [← graph.ablationMinimal_iff_inclusionMinimal]
  constructor
  · intro cap hcap
    change cap = Capability.reflectRecovery at hcap
    subst cap
    intro c hc
    exact hc
  · intro c hc hafter
    have hreq := hafter (t := Capability.reflectRecovery) (by rfl)
    have hcReq : c ∈ required Capability.reflectRecovery := by
      change c ∈ ({Condition.backwardSimulation, Condition.safetyReflection} : Set Condition)
      exact hc
    have hcDiff := hreq hcReq
    exact hcDiff.2 (by change c = c; rfl)

/-- All four conditions are inclusion-minimal for all four directional capabilities. -/
theorem allFour_minimal_for_allCapabilities :
    graph.InclusionMinimal
      {Condition.forwardSimulation, Condition.safetyPreservation,
        Condition.backwardSimulation, Condition.safetyReflection}
      Set.univ := by
  rw [← graph.ablationMinimal_iff_inclusionMinimal]
  constructor
  · intro cap hcap
    cases cap <;> intro c hc <;> simp [required] at hc ⊢ <;> aesop
  · intro c hc hafter
    cases c with
    | forwardSimulation =>
        have hreq := hafter (t := Capability.preserveViability) (Set.mem_univ _)
        have hcDiff := hreq (by simp [required])
        exact hcDiff.2 (by rfl)
    | safetyPreservation =>
        have hreq := hafter (t := Capability.preserveViability) (Set.mem_univ _)
        have hcDiff := hreq (by simp [required])
        exact hcDiff.2 (by rfl)
    | backwardSimulation =>
        have hreq := hafter (t := Capability.reflectViability) (Set.mem_univ _)
        have hcDiff := hreq (by simp [required])
        exact hcDiff.2 (by rfl)
    | safetyReflection =>
        have hreq := hafter (t := Capability.reflectViability) (Set.mem_univ _)
        have hcDiff := hreq (by simp [required])
        exact hcDiff.2 (by rfl)

end ControlDependencyGraph
end DistinctionSelfReference
