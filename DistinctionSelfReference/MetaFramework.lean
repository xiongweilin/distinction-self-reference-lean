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
  refine ⟨?_, ?_⟩
  · intro x hx
    exact hx.1
  · intro heq
    have hc' : c ∈ conditions \ {c} := by
      rw [heq]
      exact hc
    exact hc'.2 (by
      change c = c
      rfl)

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
    change x = c at hxc
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

/--
A semantic layer for condition compatibility. A realization is any model/world
on which individual conditions can be tested.
-/
structure ConditionSemantics (Condition : Type u) where
  Realization : Type v
  holds : Realization → Condition → Prop

namespace ConditionSemantics

variable {Condition : Type u}

/-- One realization satisfies every condition in the set. -/
def Satisfies
    (M : ConditionSemantics.{u, v} Condition)
    (r : M.Realization)
    (conditions : Set Condition) : Prop :=
  ∀ ⦃c⦄, c ∈ conditions → M.holds r c

/-- A condition set is compatible when some realization satisfies all of it. -/
def Compatible
    (M : ConditionSemantics.{u, v} Condition)
    (conditions : Set Condition) : Prop :=
  ∃ r, M.Satisfies r conditions

/-- Incompatibility is semantic unsatisfiability of the joint condition set. -/
def Incompatible
    (M : ConditionSemantics.{u, v} Condition)
    (conditions : Set Condition) : Prop :=
  ¬ M.Compatible conditions

/-- Compatibility is downward closed under removing conditions. -/
theorem compatible_mono
    (M : ConditionSemantics.{u, v} Condition)
    {smaller larger : Set Condition}
    (hsub : smaller ⊆ larger)
    (hcompat : M.Compatible larger) :
    M.Compatible smaller := by
  rcases hcompat with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  intro c hc
  exact hr (hsub hc)

/-- Incompatibility is upward closed under adding conditions. -/
theorem incompatible_mono
    (M : ConditionSemantics.{u, v} Condition)
    {smaller larger : Set Condition}
    (hsub : smaller ⊆ larger)
    (hincompat : M.Incompatible smaller) :
    M.Incompatible larger := by
  intro hlarge
  exact hincompat (M.compatible_mono hsub hlarge)

end ConditionSemantics
end MetaFramework
end DistinctionSelfReference
