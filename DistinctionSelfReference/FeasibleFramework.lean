import DistinctionSelfReference.MetaFramework

namespace DistinctionSelfReference
namespace MetaFramework

universe u v w

variable {Condition : Type u} {Capability : Type v}

/--
A condition set is feasibly sufficient when it both derives every requested
capability and has at least one joint semantic realization.
-/
def FeasibleSufficient
    (G : FrameworkGraph Condition Capability)
    (M : ConditionSemantics.{u, w} Condition)
    (conditions : Set Condition)
    (targets : Set Capability) : Prop :=
  M.Compatible conditions ∧ G.Sufficient conditions targets

/--
Feasible inclusion-minimality excludes proper subsets that are themselves both
jointly realizable and sufficient for the same target set.
-/
def FeasibleInclusionMinimal
    (G : FrameworkGraph Condition Capability)
    (M : ConditionSemantics.{u, w} Condition)
    (conditions : Set Condition)
    (targets : Set Capability) : Prop :=
  FeasibleSufficient G M conditions targets ∧
    ∀ ⦃smaller⦄, smaller ⊂ conditions →
      ¬ FeasibleSufficient G M smaller targets

theorem compatible_of_feasibleSufficient
    (G : FrameworkGraph Condition Capability)
    (M : ConditionSemantics.{u, w} Condition)
    {conditions : Set Condition} {targets : Set Capability}
    (h : FeasibleSufficient G M conditions targets) :
    M.Compatible conditions :=
  h.1

theorem sufficient_of_feasibleSufficient
    (G : FrameworkGraph Condition Capability)
    (M : ConditionSemantics.{u, w} Condition)
    {conditions : Set Condition} {targets : Set Capability}
    (h : FeasibleSufficient G M conditions targets) :
    G.Sufficient conditions targets :=
  h.2

/--
Ordinary sufficiency remains upward monotone, but feasibility must be checked
again after adding conditions because compatibility need not be upward closed.
-/
theorem feasibleSufficient_of_subset_of_compatible
    (G : FrameworkGraph Condition Capability)
    (M : ConditionSemantics.{u, w} Condition)
    {A B : Set Condition} {targets : Set Capability}
    (hAB : A ⊆ B)
    (hA : FeasibleSufficient G M A targets)
    (hBcompat : M.Compatible B) :
    FeasibleSufficient G M B targets := by
  exact ⟨hBcompat, G.sufficient_mono hAB hA.2⟩

/--
Any semantically incompatible condition set is automatically excluded from
feasible sufficiency, even if the derivability graph marks it sufficient.
-/
theorem not_feasibleSufficient_of_incompatible
    (G : FrameworkGraph Condition Capability)
    (M : ConditionSemantics.{u, w} Condition)
    {conditions : Set Condition} {targets : Set Capability}
    (h : M.Incompatible conditions) :
    ¬ FeasibleSufficient G M conditions targets := by
  intro hfeasible
  exact h hfeasible.1

end MetaFramework
end DistinctionSelfReference
