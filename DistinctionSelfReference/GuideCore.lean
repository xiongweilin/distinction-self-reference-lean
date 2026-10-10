/-
Guide dependency spine formalization.
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.CharZero.Infinite
import DistinctionSelfReference.MetaFramework
import DistinctionSelfReference.ConditionalComposition
import Mathlib.Order.Interval.Set.Infinite

namespace DistinctionSelfReference
namespace GuideCore

open MetaFramework
open CompositionalSufficiency
open LocalSufficiency
open Recovery
open Viability

universe u v w x y a b

/--
This revision keeps minimal self-reference on an independent branch and makes
reality-changing action the first controller-relevant capability. Only the
mathematically explicit dependency graph is represented. These constructors are dependency labels, not claims that the
corresponding philosophical notions have been reduced to one Lean datatype.
-/
inductive Condition
  | externalConstraint
  | reflexiveDistinction
  | maintainedReentry
  | identityContinuity
  | realitySideRevisability
  | realityChangingAgency
  | effectiveFinitude
  | purpose
  | exploreCommitChoice
  | localSufficiency
  | compatibility
  | recoverability
  deriving DecidableEq, Repr

inductive Capability
  | minimalSelfReference
  | persistentSelf
  | corrigibleSelfModel
  | actor
  | finiteActor
  | purposefulFiniteActor
  | localSufficiencyProblem
  | conditionalComposition
  deriving DecidableEq, Repr

/--
Guide dependency sets. Neither reflective self-reference nor corrigibility
is a prerequisite for a bounded controller.
-/
def required : Capability → Set Condition
  | .minimalSelfReference =>
      { .externalConstraint, .reflexiveDistinction, .maintainedReentry }
  | .persistentSelf =>
      { .externalConstraint, .reflexiveDistinction, .maintainedReentry,
        .identityContinuity }
  | .corrigibleSelfModel =>
      { .externalConstraint, .reflexiveDistinction, .maintainedReentry,
        .identityContinuity, .realitySideRevisability }
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
      { .localSufficiency, .compatibility, .recoverability }

def graph : FrameworkGraph Condition Capability where
  derives conditions capability := required capability ⊆ conditions
  monotone := by
    intro A B capability hAB hrequired
    exact Set.Subset.trans hrequired hAB

theorem required_minimal (capability : Capability) :
    graph.InclusionMinimal
      (required capability) {capability} := by
  constructor
  · intro target ht
    change target = capability at ht
    subst target
    exact Set.Subset.rfl
  · intro smaller hsmall hsufficient
    have hrequired := hsufficient
      (t := capability) (by rfl)
    change required capability ⊆ smaller at hrequired
    rw [Set.ssubset_iff_subset_ne] at hsmall
    exact hsmall.2
      (Set.Subset.antisymm hsmall.1 hrequired)

theorem minimalSelfReference_minimal :
    graph.InclusionMinimal
      (required .minimalSelfReference)
      {.minimalSelfReference} :=
  required_minimal .minimalSelfReference

theorem persistentSelf_minimal :
    graph.InclusionMinimal
      (required .persistentSelf)
      {.persistentSelf} :=
  required_minimal .persistentSelf

theorem actor_minimal :
    graph.InclusionMinimal
      (required .actor)
      {.actor} :=
  required_minimal .actor

theorem finiteActor_minimal :
    graph.InclusionMinimal
      (required .finiteActor)
      {.finiteActor} :=
  required_minimal .finiteActor

theorem purposefulFiniteActor_minimal :
    graph.InclusionMinimal
      (required .purposefulFiniteActor)
      {.purposefulFiniteActor} :=
  required_minimal .purposefulFiniteActor

theorem localSufficiencyProblem_minimal :
    graph.InclusionMinimal
      (required .localSufficiencyProblem)
      {.localSufficiencyProblem} :=
  required_minimal .localSufficiencyProblem

theorem conditionalComposition_minimal :
    graph.InclusionMinimal
      (required .conditionalComposition)
      {.conditionalComposition} :=
  required_minimal .conditionalComposition

/-- Self-model corrigibility is an independent strengthening branch, not an
agency prerequisite. -/
/-- There is an action-capability path that does not contain the reflexive
self-model conditions. This is an explicit graph separation, not an ontology. -/
theorem action_independent_of_reflexive_self_reference :
    Condition.reflexiveDistinction ∉ required Capability.actor ∧
    Condition.maintainedReentry ∉ required Capability.purposefulFiniteActor := by
  constructor <;> simp [required]

theorem corrigibility_branch_independent_of_agency :
    Condition.realityChangingAgency ∉
      required Capability.corrigibleSelfModel ∧
    Condition.realitySideRevisability ∉
      required Capability.actor := by
  constructor <;> simp [required]

/--
Effective finitude is local to currently effective capabilities. It does not say
that the state space itself is finite.
-/
def EffectiveFinitude
    {State : Type u}
    {EffectiveCapability : Type v}
    (available : State → Set EffectiveCapability) : Prop :=
  ∀ state, (available state).Finite

def natBoolCapabilities (_ : Nat) : Set Bool :=
  Set.univ

theorem natBool_effectivelyFinite :
    EffectiveFinitude natBoolCapabilities := by
  intro state
  exact Set.toFinite _

theorem nat_state_space_is_infinite :
    Infinite Nat :=
  inferInstance

/--
Concrete separation: per-state effective capabilities can be finite while the
state space is infinite. Thus effective finitude must not be encoded as
Fintype State.
-/
theorem effectiveFinitude_does_not_imply_finite_state :
    EffectiveFinitude natBoolCapabilities ∧ Infinite Nat :=
  ⟨natBool_effectivelyFinite, nat_state_space_is_infinite⟩

/--
At the guide layer, local sufficiency bundles the technical coverage premise
used by the existing compositional theorem with local sufficiency itself.
Coverage is therefore not promoted to a new philosophical primitive.
-/
structure LocalSufficiencyEvidence
    {Index : Type u} {World : Type v} {Obs : Type w}
    {Var : Type x} {Value : Type y}
    (R : LocalRequirement Index World Obs Var Value) : Prop where
  covers : R.Covers
  locallySufficient : R.LocallySufficient

/--
The guide composition spine is backed by the existing constructive theorem:
local sufficiency + compatibility + minimum recoverability yields a conditional
composition witness.

World and State remain arbitrary types; neither is assumed finite or
exhaustively enumerable.
-/
noncomputable def conditionalCompositionWitness
    {Index : Type u} {World : Type v} {Obs : Type w}
    {Var : Type x} {Value : Type y}
    {State : Type a} {Action : Type b}
    (R : LocalRequirement Index World Obs Var Value)
    (C : ControlledSystem State Action)
    (hlocal : LocalSufficiencyEvidence R)
    (hcompat : R.Compatible)
    (world : World)
    (state : State)
    (hrecover : Recoverable C state) :
    ConditionalComposition.Witness R C world state :=
  ConditionalComposition.witness_of_localSufficiency_compatibility_recoverability
    R C
    hlocal.covers
    hcompat
    hlocal.locallySufficient
    world state hrecover

end GuideCore
end DistinctionSelfReference
