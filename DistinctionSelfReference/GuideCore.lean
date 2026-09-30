/-
Guide dependency spine formalization.
-/
import DistinctionSelfReference.MetaFramework
import DistinctionSelfReference.ConditionalComposition

namespace DistinctionSelfReference
namespace GuideCore

open MetaFramework
open CompositionalSufficiency
open LocalSufficiency
open Recovery
open Viability

universe u v w x y a b

/--
Only the mathematically explicit dependency spine from the guide repository is
represented here. These constructors are dependency labels, not claims that the
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
Guide dependency sets. The corrigibility/self-revision branch is intentionally
not a prerequisite for becoming an actor.
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
      { .externalConstraint, .reflexiveDistinction, .maintainedReentry,
        .identityContinuity, .realityChangingAgency }
  | .finiteActor =>
      { .externalConstraint, .reflexiveDistinction, .maintainedReentry,
        .identityContinuity, .realityChangingAgency, .effectiveFinitude }
  | .purposefulFiniteActor =>
      { .externalConstraint, .reflexiveDistinction, .maintainedReentry,
        .identityContinuity, .realityChangingAgency, .effectiveFinitude,
        .purpose }
  | .localSufficiencyProblem =>
      { .externalConstraint, .reflexiveDistinction, .maintainedReentry,
        .identityContinuity, .realityChangingAgency, .effectiveFinitude,
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
    exact (Set.not_subset_of_ssubset hsmall) hrequired

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
  exact Set.finite_univ

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
