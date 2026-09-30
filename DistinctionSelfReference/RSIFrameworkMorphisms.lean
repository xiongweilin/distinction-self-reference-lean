import DistinctionSelfReference.FrameworkMorphism
import DistinctionSelfReference.FullRSIInvariantCore

namespace DistinctionSelfReference
namespace RSIFrameworkMorphisms

open MetaFramework
open FrameworkMorphisms

abbrev Role := FullRSIInvariantCore.Role

/--
The shared role framework derives a requested role-set exactly when all of those
roles are present among the translated conditions.
-/
def roleGraph : FrameworkGraph Role (Set Role) where
  derives conditions requiredRoles := requiredRoles ⊆ conditions
  monotone := by
    intro A B roles hAB hroles
    exact Set.Subset.trans hroles hAB

def advancedFramework :=
  Framework.free AdvancedRSIDependencyGraph.graph

def nextFramework :=
  Framework.free NextRSIDependencyGraph.graph

def roleFramework :=
  Framework.free roleGraph

/-- The semantic-role requirement of one advanced-RSI capability. -/
def advancedCapabilityRoles
    (capability : AdvancedRSIDependencyGraph.Capability) :
    Set Role :=
  FullRSIInvariantCore.advancedMap ''
    AdvancedRSIDependencyGraph.required capability

/-- The semantic-role requirement of one next-phase RSI capability. -/
def nextCapabilityRoles
    (capability : NextRSIDependencyGraph.Capability) :
    Set Role :=
  FullRSIInvariantCore.nextMap ''
    NextRSIDependencyGraph.required capability

theorem advanced_derivation_preserved
    {conditions : Set AdvancedRSIDependencyGraph.Condition}
    {capability : AdvancedRSIDependencyGraph.Capability}
    (h :
      AdvancedRSIDependencyGraph.graph.derives
        conditions capability) :
    roleGraph.derives
      (FullRSIInvariantCore.advancedMap '' conditions)
      (advancedCapabilityRoles capability) := by
  intro role hrole
  rcases hrole with ⟨condition, hrequired, rfl⟩
  exact ⟨condition, h hrequired, rfl⟩

theorem next_derivation_preserved
    {conditions : Set NextRSIDependencyGraph.Condition}
    {capability : NextRSIDependencyGraph.Capability}
    (h :
      NextRSIDependencyGraph.graph.derives
        conditions capability) :
    roleGraph.derives
      (FullRSIInvariantCore.nextMap '' conditions)
      (nextCapabilityRoles capability) := by
  intro role hrole
  rcases hrole with ⟨condition, hrequired, rfl⟩
  exact ⟨condition, h hrequired, rfl⟩

/--
The old advanced role map is now part of a certified framework morphism rather
than a standalone manually interpreted function.
-/
def advancedMorphism :
    FrameworkMorphism advancedFramework roleFramework :=
  FrameworkMorphism.freeMorphism
    AdvancedRSIDependencyGraph.graph
    roleGraph
    FullRSIInvariantCore.advancedMap
    advancedCapabilityRoles
    advanced_derivation_preserved

/-- The next-phase role translation is certified in the same shared target. -/
def nextMorphism :
    FrameworkMorphism nextFramework roleFramework :=
  FrameworkMorphism.freeMorphism
    NextRSIDependencyGraph.graph
    roleGraph
    FullRSIInvariantCore.nextMap
    nextCapabilityRoles
    next_derivation_preserved

/--
The invariant role core is now defined from the condition images of certified
framework morphisms.
-/
def morphismRoleCore : Set Role :=
  InvariantConditionCore
    advancedMorphism FullRSIInvariantCore.advancedConditions
    nextMorphism FullRSIInvariantCore.nextConditions

theorem morphismRoleCore_eq_univ :
    morphismRoleCore = Set.univ := by
  ext role
  constructor
  · intro _
    trivial
  · intro _
    change
      role ∈
          FullRSIInvariantCore.advancedMap ''
            FullRSIInvariantCore.advancedConditions ∧
        role ∈
          FullRSIInvariantCore.nextMap ''
            FullRSIInvariantCore.nextConditions
    constructor
    · rcases FullRSIInvariantCore.advanced_covers_all role with
        ⟨condition, hcondition, hmap⟩
      exact ⟨condition, hcondition, hmap⟩
    · rcases FullRSIInvariantCore.next_covers_all role with
        ⟨condition, hcondition, hmap⟩
      exact ⟨condition, hcondition, hmap⟩

/--
The certified-morphism definition recovers the previous manually defined full
role core, while moving the translation maps inside compositional proof-carrying
structure.
-/
theorem morphismRoleCore_eq_legacy_fullCore :
    morphismRoleCore = FullRSIInvariantCore.fullCore := by
  rw [morphismRoleCore_eq_univ,
    FullRSIInvariantCore.fullCore_eq_univ]

end RSIFrameworkMorphisms
end DistinctionSelfReference
