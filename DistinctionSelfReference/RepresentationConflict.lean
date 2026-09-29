import DistinctionSelfReference.MetaFramework
import DistinctionSelfReference.RepresentationalObstruction

namespace DistinctionSelfReference
namespace RepresentationConflict

open MetaFramework

universe u v

/-- Two assumptions whose coexistence is ruled out by the Lawvere argument. -/
inductive Condition
  | fixedPointFreeEndomap
  | universalSurjectiveRepresentation
  deriving DecidableEq, Repr

/-- A concrete world carrying both an evaluator and an endomap. -/
structure Scenario (Alpha : Type u) (Beta : Type v) where
  eval : Alpha → Alpha → Beta
  step : Beta → Beta

/-- Interpret the two abstract conditions in one representational scenario. -/
def semantics (Alpha : Type u) (Beta : Type v) :
    ConditionSemantics Condition where
  Realization := Scenario Alpha Beta
  holds s c :=
    match c with
    | .fixedPointFreeEndomap => ∀ x, s.step x ≠ x
    | .universalSurjectiveRepresentation => Function.Surjective s.eval

/-- The two conditions are semantically incompatible in every type pair. -/
theorem lawvere_pair_incompatible
    (Alpha : Type u) (Beta : Type v) :
    (semantics Alpha Beta).Incompatible
      {Condition.fixedPointFreeEndomap,
       Condition.universalSurjectiveRepresentation} := by
  rintro ⟨s, hs⟩
  have hfree : ∀ x, s.step x ≠ x :=
    hs (c := Condition.fixedPointFreeEndomap) (by
      change Condition.fixedPointFreeEndomap =
        Condition.fixedPointFreeEndomap ∨
        Condition.fixedPointFreeEndomap =
          Condition.universalSurjectiveRepresentation
      exact Or.inl rfl)
  have hsurj : Function.Surjective s.eval :=
    hs (c := Condition.universalSurjectiveRepresentation) (by
      change Condition.universalSurjectiveRepresentation =
        Condition.fixedPointFreeEndomap ∨
        Condition.universalSurjectiveRepresentation =
          Condition.universalSurjectiveRepresentation
      exact Or.inr rfl)
  exact RepresentationalObstruction.fixedPointFree_forbids_surjective_representation
    s.step hfree ⟨s.eval, hsurj⟩

/--
The conflict therefore persists in every larger condition set containing both
representational assumptions.
-/
theorem lawvere_conflict_upward
    (Alpha : Type u) (Beta : Type v)
    {conditions : Set Condition}
    (hpair :
      ({Condition.fixedPointFreeEndomap,
        Condition.universalSurjectiveRepresentation} : Set Condition) ⊆ conditions) :
    (semantics Alpha Beta).Incompatible conditions := by
  exact (semantics Alpha Beta).incompatible_mono hpair
    (lawvere_pair_incompatible Alpha Beta)

end RepresentationConflict
end DistinctionSelfReference
