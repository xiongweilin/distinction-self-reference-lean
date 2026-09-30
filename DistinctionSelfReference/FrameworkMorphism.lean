import DistinctionSelfReference.FeasibleFramework

namespace DistinctionSelfReference
namespace FrameworkMorphisms

open MetaFramework

universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃

/--
A framework packages the monotone derivability graph together with a semantic
realization space for its conditions.
-/
structure Framework
    (Condition : Type u₁)
    (Capability : Type v₁)
    (Realization : Type w₁) where
  graph : FrameworkGraph Condition Capability
  holds : Realization → Condition → Prop

namespace Framework

variable {Condition : Type u₁} {Capability : Type v₁}
  {Realization : Type w₁}

def semantics
    (F : Framework Condition Capability Realization) :
    ConditionSemantics.{u₁, w₁} Condition where
  Realization := Realization
  holds := F.holds

def Satisfies
    (F : Framework Condition Capability Realization)
    (r : Realization)
    (conditions : Set Condition) : Prop :=
  ∀ ⦃c⦄, c ∈ conditions → F.holds r c

def Compatible
    (F : Framework Condition Capability Realization)
    (conditions : Set Condition) : Prop :=
  ∃ r, F.Satisfies r conditions

theorem compatible_iff_semantics
    (F : Framework Condition Capability Realization)
    (conditions : Set Condition) :
    F.Compatible conditions ↔
      F.semantics.Compatible conditions :=
  Iff.rfl

/--
The freely realized form of a derivability graph. A realization is simply a set
of conditions and a condition holds exactly when it belongs to that set.

This is useful for purely structural translations: every condition set is
compatible, without pretending that this supplies the domain-specific semantics
used by incompatibility results elsewhere in the repository.
-/
def free
    (G : FrameworkGraph Condition Capability) :
    Framework Condition Capability (Set Condition) where
  graph := G
  holds := fun realization condition => condition ∈ realization

theorem free_compatible
    (G : FrameworkGraph Condition Capability)
    (conditions : Set Condition) :
    (free G).Compatible conditions := by
  exact ⟨conditions, fun _ hc => hc⟩

end Framework

/--
A structure-preserving translation between frameworks.

Besides translating conditions and capabilities, it translates semantic
realizations and proves satisfaction preservation. This makes compatibility
preservation a theorem rather than an extra opaque field.
-/
structure FrameworkMorphism
    {SourceCondition : Type u₁}
    {SourceCapability : Type v₁}
    {SourceRealization : Type w₁}
    {TargetCondition : Type u₂}
    {TargetCapability : Type v₂}
    {TargetRealization : Type w₂}
    (source :
      Framework SourceCondition SourceCapability SourceRealization)
    (target :
      Framework TargetCondition TargetCapability TargetRealization) where
  mapCondition : SourceCondition → TargetCondition
  mapCapability : SourceCapability → TargetCapability
  mapRealization : SourceRealization → TargetRealization
  preservesCondition :
    ∀ {r c},
      source.holds r c →
      target.holds (mapRealization r) (mapCondition c)
  preservesDerivation :
    ∀ {conditions capability},
      source.graph.derives conditions capability →
      target.graph.derives
        (mapCondition '' conditions)
        (mapCapability capability)

namespace FrameworkMorphism

variable
    {C₁ : Type u₁} {K₁ : Type v₁} {R₁ : Type w₁}
    {C₂ : Type u₂} {K₂ : Type v₂} {R₂ : Type w₂}
    {C₃ : Type u₃} {K₃ : Type v₃} {R₃ : Type w₃}
    {F : Framework C₁ K₁ R₁}
    {G : Framework C₂ K₂ R₂}
    {H : Framework C₃ K₃ R₃}

def mapConditions
    (m : FrameworkMorphism F G)
    (conditions : Set C₁) :
    Set C₂ :=
  m.mapCondition '' conditions

def mapCapabilities
    (m : FrameworkMorphism F G)
    (capabilities : Set K₁) :
    Set K₂ :=
  m.mapCapability '' capabilities

theorem preservesSatisfaction
    (m : FrameworkMorphism F G)
    {r : R₁} {conditions : Set C₁}
    (h : F.Satisfies r conditions) :
    G.Satisfies (m.mapRealization r) (m.mapConditions conditions) := by
  intro c hc
  rcases hc with ⟨sourceCondition, hs, rfl⟩
  exact m.preservesCondition (h hs)

theorem preservesCompatibility
    (m : FrameworkMorphism F G)
    {conditions : Set C₁}
    (h : F.Compatible conditions) :
    G.Compatible (m.mapConditions conditions) := by
  rcases h with ⟨r, hr⟩
  exact ⟨m.mapRealization r, m.preservesSatisfaction hr⟩

def identity
    (F : Framework C₁ K₁ R₁) :
    FrameworkMorphism F F where
  mapCondition := id
  mapCapability := id
  mapRealization := id
  preservesCondition := fun h => h
  preservesDerivation := by
    intro conditions capability h
    simpa using h

def comp
    (m₁₂ : FrameworkMorphism F G)
    (m₂₃ : FrameworkMorphism G H) :
    FrameworkMorphism F H where
  mapCondition := m₂₃.mapCondition ∘ m₁₂.mapCondition
  mapCapability := m₂₃.mapCapability ∘ m₁₂.mapCapability
  mapRealization := m₂₃.mapRealization ∘ m₁₂.mapRealization
  preservesCondition := by
    intro r c h
    exact m₂₃.preservesCondition (m₁₂.preservesCondition h)
  preservesDerivation := by
    intro conditions capability h
    have h₁ := m₁₂.preservesDerivation h
    have h₂ := m₂₃.preservesDerivation h₁
    simpa [Set.image_image, Function.comp_def] using h₂

@[simp] theorem identity_mapCondition
    (F : Framework C₁ K₁ R₁)
    (c : C₁) :
    (identity F).mapCondition c = c :=
  rfl

@[simp] theorem identity_mapCapability
    (F : Framework C₁ K₁ R₁)
    (capability : K₁) :
    (identity F).mapCapability capability = capability :=
  rfl

@[simp] theorem comp_mapCondition
    (m₁₂ : FrameworkMorphism F G)
    (m₂₃ : FrameworkMorphism G H)
    (c : C₁) :
    (comp m₁₂ m₂₃).mapCondition c =
      m₂₃.mapCondition (m₁₂.mapCondition c) :=
  rfl

@[simp] theorem comp_mapCapability
    (m₁₂ : FrameworkMorphism F G)
    (m₂₃ : FrameworkMorphism G H)
    (capability : K₁) :
    (comp m₁₂ m₂₃).mapCapability capability =
      m₂₃.mapCapability (m₁₂.mapCapability capability) :=
  rfl

/--
A graph-level derivation translation canonically lifts to a framework morphism
between freely realized frameworks.
-/
def freeMorphism
    (sourceGraph : FrameworkGraph C₁ K₁)
    (targetGraph : FrameworkGraph C₂ K₂)
    (mapCondition : C₁ → C₂)
    (mapCapability : K₁ → K₂)
    (preservesDerivation :
      ∀ {conditions capability},
        sourceGraph.derives conditions capability →
        targetGraph.derives
          (mapCondition '' conditions)
          (mapCapability capability)) :
    FrameworkMorphism
      (Framework.free sourceGraph)
      (Framework.free targetGraph) where
  mapCondition := mapCondition
  mapCapability := mapCapability
  mapRealization := fun realization => mapCondition '' realization
  preservesCondition := by
    intro realization condition hc
    exact ⟨condition, hc, rfl⟩
  preservesDerivation := preservesDerivation

/-- Sufficiency transports along any framework morphism. -/
theorem preservesSufficient
    (m : FrameworkMorphism F G)
    {conditions : Set C₁}
    {targets : Set K₁}
    (h : F.graph.Sufficient conditions targets) :
    G.graph.Sufficient
      (m.mapConditions conditions)
      (m.mapCapabilities targets) := by
  intro target ht
  rcases ht with ⟨sourceTarget, hs, rfl⟩
  exact m.preservesDerivation (h hs)

/-- Feasible sufficiency also transports because morphisms preserve both
derivation and semantic compatibility. -/
theorem preservesFeasibleSufficient
    (m : FrameworkMorphism F G)
    {conditions : Set C₁}
    {targets : Set K₁}
    (h :
      FeasibleSufficient
        F.graph F.semantics conditions targets) :
    FeasibleSufficient
      G.graph G.semantics
      (m.mapConditions conditions)
      (m.mapCapabilities targets) := by
  exact ⟨m.preservesCompatibility h.1,
    m.preservesSufficient h.2⟩

/-- A morphism reflects derivation when no source derivation is created merely
by translating into the target framework. -/
def ReflectsDerivation
    (m : FrameworkMorphism F G) : Prop :=
  ∀ {conditions capability},
    G.graph.derives
      (m.mapConditions conditions)
      (m.mapCapability capability) →
    F.graph.derives conditions capability

/--
Source dominance is preserved on translated capabilities when derivability is
both preserved and reflected.
-/
theorem preservesMappedDominance
    (m : FrameworkMorphism F G)
    {A B : Set C₁}
    (hreflect : m.ReflectsDerivation)
    (hdom : F.graph.Dominates A B) :
    ∀ capability,
      G.graph.derives
        (m.mapConditions B)
        (m.mapCapability capability) →
      G.graph.derives
        (m.mapConditions A)
        (m.mapCapability capability) := by
  intro capability hB
  exact m.preservesDerivation
    (hdom capability (hreflect hB))

/--
If every target capability is represented by a source capability, reflected
derivability upgrades mapped dominance to ordinary target-framework dominance.
-/
theorem preservesDominance_of_surjective
    (m : FrameworkMorphism F G)
    {A B : Set C₁}
    (hreflect : m.ReflectsDerivation)
    (hsurj : Function.Surjective m.mapCapability)
    (hdom : F.graph.Dominates A B) :
    G.graph.Dominates
      (m.mapConditions A)
      (m.mapConditions B) := by
  intro targetCapability hB
  rcases hsurj targetCapability with ⟨sourceCapability, rfl⟩
  exact m.preservesMappedDominance hreflect hdom sourceCapability hB

end FrameworkMorphism

/--
The invariant condition core induced by two certified translations into one
shared target framework.
-/
def InvariantConditionCore
    {C₁ : Type u₁} {K₁ : Type v₁} {R₁ : Type w₁}
    {C₂ : Type u₂} {K₂ : Type v₂} {R₂ : Type w₂}
    {C : Type u₃} {K : Type v₃} {R : Type w₃}
    {F₁ : Framework C₁ K₁ R₁}
    {F₂ : Framework C₂ K₂ R₂}
    {Core : Framework C K R}
    (m₁ : FrameworkMorphism F₁ Core)
    (conditions₁ : Set C₁)
    (m₂ : FrameworkMorphism F₂ Core)
    (conditions₂ : Set C₂) :
    Set C :=
  m₁.mapConditions conditions₁ ∩
  m₂.mapConditions conditions₂

theorem mem_invariantConditionCore_iff
    {C₁ : Type u₁} {K₁ : Type v₁} {R₁ : Type w₁}
    {C₂ : Type u₂} {K₂ : Type v₂} {R₂ : Type w₂}
    {C : Type u₃} {K : Type v₃} {R : Type w₃}
    {F₁ : Framework C₁ K₁ R₁}
    {F₂ : Framework C₂ K₂ R₂}
    {Core : Framework C K R}
    (m₁ : FrameworkMorphism F₁ Core)
    (conditions₁ : Set C₁)
    (m₂ : FrameworkMorphism F₂ Core)
    (conditions₂ : Set C₂)
    (c : C) :
    c ∈ InvariantConditionCore m₁ conditions₁ m₂ conditions₂ ↔
      (∃ source, source ∈ conditions₁ ∧ m₁.mapCondition source = c) ∧
      (∃ source, source ∈ conditions₂ ∧ m₂.mapCondition source = c) := by
  rfl

end FrameworkMorphisms
end DistinctionSelfReference
