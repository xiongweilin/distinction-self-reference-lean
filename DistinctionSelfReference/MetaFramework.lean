import Mathlib.Data.Set.Basic

namespace DistinctionSelfReference
namespace MetaFramework

universe u v

/--
A monotone condition/capability graph. Adding assumptions may add capabilities
but cannot invalidate a capability already derivable.
-/
structure FrameworkGraph (Condition : Type u) (Capability : Type v) where
  derives : Set Condition → Capability → Prop
  monotone : ∀ ⦃A B t⦄, A ⊆ B → derives A t → derives B t

namespace FrameworkGraph

variable {Condition : Type u} {Capability : Type v}

/-- A condition set is sufficient for every capability in the target set. -/
def Sufficient
    (G : FrameworkGraph Condition Capability)
    (conditions : Set Condition)
    (targets : Set Capability) : Prop :=
  ∀ ⦃t⦄, t ∈ targets → G.derives conditions t

theorem sufficient_mono
    (G : FrameworkGraph Condition Capability)
    {A B : Set Condition} {targets : Set Capability}
    (hAB : A ⊆ B)
    (hA : G.Sufficient A targets) :
    G.Sufficient B targets := by
  intro t ht
  exact G.monotone hAB (hA ht)

/--
Single-condition ablation minimality: the target is sufficient, but removing
any condition currently present destroys sufficiency.
-/
def AblationMinimal
    (G : FrameworkGraph Condition Capability)
    (conditions : Set Condition)
    (targets : Set Capability) : Prop :=
  G.Sufficient conditions targets ∧
    ∀ ⦃c⦄, c ∈ conditions →
      ¬ G.Sufficient (conditions \ {c}) targets

/--
Inclusion minimality: no proper subset of the condition set is sufficient.
-/
def InclusionMinimal
    (G : FrameworkGraph Condition Capability)
    (conditions : Set Condition)
    (targets : Set Capability) : Prop :=
  G.Sufficient conditions targets ∧
    ∀ ⦃smaller⦄, smaller ⊂ conditions →
      ¬ G.Sufficient smaller targets

/-- Inclusion minimality implies failure of every one-condition ablation. -/
theorem ablationMinimal_of_inclusionMinimal
    (G : FrameworkGraph Condition Capability)
    {conditions : Set Condition} {targets : Set Capability}
    (hmin : G.InclusionMinimal conditions targets) :
    G.AblationMinimal conditions targets := by
  refine ⟨hmin.1, ?_⟩
  intro c hc
  apply hmin.2
  rw [Set.ssubset_iff_subset_ne]
  refine ⟨Set.sdiff_subset, ?_⟩
  intro heq
  have hc' : c ∈ conditions \ {c} := by
    rw [heq]
    exact hc
  simpa using hc'

/--
For a monotone capability relation, single-condition ablation minimality is
already enough to rule out every proper sufficient subset.
-/
theorem inclusionMinimal_of_ablationMinimal
    (G : FrameworkGraph Condition Capability)
    {conditions : Set Condition} {targets : Set Capability}
    (habl : G.AblationMinimal conditions targets) :
    G.InclusionMinimal conditions targets := by
  refine ⟨habl.1, ?_⟩
  intro smaller hsmall hSufficient
  rcases Set.exists_of_ssubset hsmall with ⟨c, hc, hcnot⟩
  have hsub : smaller ⊆ conditions \ {c} := by
    intro x hx
    refine ⟨hsmall.1 hx, ?_⟩
    intro hxc
    have : x = c := by simpa using hxc
    subst x
    exact hcnot hx
  have hAfterDelete :
      G.Sufficient (conditions \ {c}) targets :=
    G.sufficient_mono hsub hSufficient
  exact (habl.2 hc) hAfterDelete

/--
Under monotonicity, the practical one-condition ablation test exactly
characterizes inclusion-minimal sufficient frameworks.
-/
theorem ablationMinimal_iff_inclusionMinimal
    (G : FrameworkGraph Condition Capability)
    (conditions : Set Condition)
    (targets : Set Capability) :
    G.AblationMinimal conditions targets ↔
      G.InclusionMinimal conditions targets := by
  constructor
  · exact G.inclusionMinimal_of_ablationMinimal
  · exact G.ablationMinimal_of_inclusionMinimal

/-- One condition set dominates another when it derives every capability the other derives. -/
def Dominates
    (G : FrameworkGraph Condition Capability)
    (strong weak : Set Condition) : Prop :=
  ∀ t, G.derives weak t → G.derives strong t

/-- Set inclusion always induces capability dominance. -/
theorem dominates_of_subset
    (G : FrameworkGraph Condition Capability)
    {weak strong : Set Condition}
    (h : weak ⊆ strong) :
    G.Dominates strong weak := by
  intro t ht
  exact G.monotone h ht

/-- Two condition sets are capability-equivalent when they derive the same capabilities. -/
def CapabilityEquivalent
    (G : FrameworkGraph Condition Capability)
    (A B : Set Condition) : Prop :=
  ∀ t, G.derives A t ↔ G.derives B t

theorem capabilityEquivalent_iff_mutualDominance
    (G : FrameworkGraph Condition Capability)
    (A B : Set Condition) :
    G.CapabilityEquivalent A B ↔
      G.Dominates A B ∧ G.Dominates B A := by
  constructor
  · intro h
    constructor
    · intro t ht
      exact (h t).mpr ht
    · intro t ht
      exact (h t).mp ht
  · rintro ⟨hAB, hBA⟩
    intro t
    exact ⟨hBA t, hAB t⟩

end FrameworkGraph
end MetaFramework
end DistinctionSelfReference
