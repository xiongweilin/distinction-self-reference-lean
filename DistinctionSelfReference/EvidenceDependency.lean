import Mathlib.Logic.Relation
import DistinctionSelfReference.EvaluatorProvenance

namespace DistinctionSelfReference
namespace EvidenceDependency

open EvaluatorProvenance

universe u v

/--
An evidence item is dependency-current when it is itself current and every
transitively required premise is also current.
-/
def DependencyCurrent
    {Version : Type u}
    {Claim : Type v}
    (preserves : Version → Version → Prop)
    (current : Version)
    (dependsOn :
      Evidence Version Claim → Evidence Version Claim → Prop)
    (e : Evidence Version Claim) : Prop :=
  CurrentEvidence preserves current e ∧
  ∀ d,
    Relation.TransGen dependsOn e d →
    CurrentEvidence preserves current d

/-- Current dependency-qualified history is a filter over immutable history. -/
def DependencyCurrentHistory
    {Version : Type u}
    {Claim : Type v}
    (preserves : Version → Version → Prop)
    (current : Version)
    (dependsOn :
      Evidence Version Claim → Evidence Version Claim → Prop)
    (history : Set (Evidence Version Claim)) :
    Set (Evidence Version Claim) :=
  {e | e ∈ history ∧ DependencyCurrent preserves current dependsOn e}

theorem dependencyCurrentHistory_subset_history
    {Version : Type u}
    {Claim : Type v}
    (preserves : Version → Version → Prop)
    (current : Version)
    (dependsOn :
      Evidence Version Claim → Evidence Version Claim → Prop)
    (history : Set (Evidence Version Claim)) :
    DependencyCurrentHistory preserves current dependsOn history ⊆ history := by
  intro e he
  exact he.1

/-- One preservation policy extends another when every previously justified
migration remains justified. -/
def PreservationExtends
    {Version : Type u}
    (oldPolicy newPolicy : Version → Version → Prop) : Prop :=
  ∀ a b, oldPolicy a b → newPolicy a b

theorem currentEvidence_mono_preservation
    {Version : Type u}
    {Claim : Type v}
    {oldPolicy newPolicy : Version → Version → Prop}
    (hext : PreservationExtends oldPolicy newPolicy)
    (current : Version)
    (e : Evidence Version Claim)
    (hcurrent : CurrentEvidence oldPolicy current e) :
    CurrentEvidence newPolicy current e := by
  cases hs : e.source with
  | anchor =>
      rw [CurrentEvidence, hs]
      trivial
  | evaluator old =>
      rw [CurrentEvidence, hs] at hcurrent ⊢
      rcases hcurrent with heq | hpres
      · exact Or.inl heq
      · exact Or.inr (hext old current hpres)

theorem dependencyCurrent_mono_preservation
    {Version : Type u}
    {Claim : Type v}
    {oldPolicy newPolicy : Version → Version → Prop}
    (hext : PreservationExtends oldPolicy newPolicy)
    (current : Version)
    (dependsOn :
      Evidence Version Claim → Evidence Version Claim → Prop)
    (e : Evidence Version Claim)
    (hcurrent : DependencyCurrent oldPolicy current dependsOn e) :
    DependencyCurrent newPolicy current dependsOn e := by
  constructor
  · exact currentEvidence_mono_preservation
      hext current e hcurrent.1
  · intro d hd
    exact currentEvidence_mono_preservation
      hext current d (hcurrent.2 d hd)

theorem dependencyCurrentHistory_mono_preservation
    {Version : Type u}
    {Claim : Type v}
    {oldPolicy newPolicy : Version → Version → Prop}
    (hext : PreservationExtends oldPolicy newPolicy)
    (current : Version)
    (dependsOn :
      Evidence Version Claim → Evidence Version Claim → Prop)
    (history : Set (Evidence Version Claim)) :
    DependencyCurrentHistory oldPolicy current dependsOn history ⊆
      DependencyCurrentHistory newPolicy current dependsOn history := by
  intro e he
  exact ⟨he.1,
    dependencyCurrent_mono_preservation
      hext current dependsOn e he.2⟩

/--
If a direct premise is no longer current after migration, every conclusion
that depends on it loses dependency-current qualification.
-/
theorem stale_direct_dependency_invalidates
    {Version : Type u}
    {Claim : Type v}
    (preserves : Version → Version → Prop)
    (current : Version)
    (dependsOn :
      Evidence Version Claim → Evidence Version Claim → Prop)
    {e d : Evidence Version Claim}
    (hdep : dependsOn e d)
    (hstale : ¬ CurrentEvidence preserves current d) :
    ¬ DependencyCurrent preserves current dependsOn e := by
  intro hcurrent
  exact hstale (hcurrent.2 d (Relation.TransGen.single hdep))

/--
The same invalidation propagates through an arbitrary finite dependency chain.
-/
theorem stale_transitive_dependency_invalidates
    {Version : Type u}
    {Claim : Type v}
    (preserves : Version → Version → Prop)
    (current : Version)
    (dependsOn :
      Evidence Version Claim → Evidence Version Claim → Prop)
    {e d : Evidence Version Claim}
    (hdep : Relation.TransGen dependsOn e d)
    (hstale : ¬ CurrentEvidence preserves current d) :
    ¬ DependencyCurrent preserves current dependsOn e := by
  intro hcurrent
  exact hstale (hcurrent.2 d hdep)

/--
Anchor-only dependency chains survive evaluator migration whenever the
conclusion itself remains current.
-/
theorem anchor_dependencies_survive
    {Version : Type u}
    {Claim : Type v}
    (preserves : Version → Version → Prop)
    (current : Version)
    (dependsOn :
      Evidence Version Claim → Evidence Version Claim → Prop)
    (e : Evidence Version Claim)
    (he : CurrentEvidence preserves current e)
    (hanchor :
      ∀ d,
        Relation.TransGen dependsOn e d →
        d.source = .anchor) :
    DependencyCurrent preserves current dependsOn e := by
  constructor
  · exact he
  · intro d hd
    rw [CurrentEvidence, hanchor d hd]
    trivial

namespace SelectiveCascadeExample

inductive Version
  | old
  | current
  deriving DecidableEq, Repr

inductive Claim
  | reality
  | oldJudgment
  | derived
  | independent
  deriving DecidableEq, Repr

def reality : Evidence Version Claim :=
  ⟨.reality, .anchor⟩

def oldJudgment : Evidence Version Claim :=
  ⟨.oldJudgment, .evaluator .old⟩

def derived : Evidence Version Claim :=
  ⟨.derived, .anchor⟩

def independent : Evidence Version Claim :=
  ⟨.independent, .anchor⟩

/-- The derived claim depends on stale evaluator evidence; the independent
claim depends only on reality evidence. -/
def dependsOn : Evidence Version Claim → Evidence Version Claim → Prop
  | e, d =>
      (e = derived ∧ d = oldJudgment) ∨
      (e = independent ∧ d = reality)

def preserves (_ _ : Version) : Prop := False

theorem oldJudgment_stale :
    ¬ CurrentEvidence preserves .current oldJudgment := by
  rw [CurrentEvidence]
  exact stale_evaluator_source_not_current
    preserves
    (by decide)
    (by simp [preserves])

theorem derived_invalidated :
    ¬ DependencyCurrent preserves .current dependsOn derived := by
  apply stale_direct_dependency_invalidates
    preserves .current dependsOn
    (d := oldJudgment)
  · exact Or.inl ⟨rfl, rfl⟩
  · exact oldJudgment_stale

theorem reality_current :
    CurrentEvidence preserves .current reality := by
  rw [CurrentEvidence]
  exact anchor_source_always_current preserves .current

theorem independent_dependency_path_ends_at_reality
    {d : Evidence Version Claim}
    (hd : Relation.TransGen dependsOn independent d) :
    d = reality := by
  induction hd with
  | single h =>
      rcases h with h | h
      · exact False.elim (by
          rcases h with ⟨hbad, _⟩
          simpa [derived, independent] using hbad)
      · exact h.2
  | tail hpath hlast ih =>
      subst_vars
      exfalso
      simpa [dependsOn, reality, derived, independent, oldJudgment] using hlast

theorem independent_current :
    DependencyCurrent preserves .current dependsOn independent := by
  apply anchor_dependencies_survive
  · rw [CurrentEvidence]
    exact anchor_source_always_current preserves .current
  · intro d hd
    rw [independent_dependency_path_ends_at_reality hd]
    rfl

/--
Selective cascade: migration invalidates the claim whose proof depends on stale
evaluator evidence, while an independent claim supported only by reality
evidence remains current.
-/
theorem migration_selectively_cascades :
    ¬ DependencyCurrent preserves .current dependsOn derived ∧
      DependencyCurrent preserves .current dependsOn independent :=
  ⟨derived_invalidated, independent_current⟩

/-- A later bridge can explicitly justify migration of the old evaluator
evidence without changing historical records. -/
def repairedPreserves (old new : Version) : Prop :=
  old = .old ∧ new = .current

theorem preserves_extends_to_repaired :
    PreservationExtends preserves repairedPreserves := by
  intro a b hab
  simp [preserves] at hab

theorem oldJudgment_revalidated :
    CurrentEvidence repairedPreserves .current oldJudgment := by
  rw [CurrentEvidence]
  exact Or.inr ⟨rfl, rfl⟩

theorem reality_revalidated :
    CurrentEvidence repairedPreserves .current reality := by
  rw [CurrentEvidence]
  exact anchor_source_always_current repairedPreserves .current

/--
Once the evaluator bridge is supplied, the previously stale derived conclusion
becomes dependency-current again. The independent reality-supported conclusion
remains current throughout.
-/
theorem derived_dependency_path_ends_at_oldJudgment
    {d : Evidence Version Claim}
    (hd : Relation.TransGen dependsOn derived d) :
    d = oldJudgment := by
  induction hd with
  | single h =>
      rcases h with h | h
      · exact h.2
      · exact False.elim (by
          rcases h with ⟨hbad, _⟩
          simp [derived, independent] at hbad)
  | tail hpath hlast ih =>
      subst_vars
      exfalso
      simpa [dependsOn, oldJudgment, derived, independent, reality] using hlast

theorem repaired_bridge_restores_derived :
    DependencyCurrent repairedPreserves .current dependsOn derived := by
  constructor
  · rw [CurrentEvidence]
    exact anchor_source_always_current repairedPreserves .current
  · intro d hd
    rw [derived_dependency_path_ends_at_oldJudgment hd]
    exact oldJudgment_revalidated

/--
Revalidation is selective and monotone: adding a justified preservation bridge
can restore stale conclusions without invalidating conclusions that were
already current.
-/
theorem selective_revalidation :
    (¬ DependencyCurrent preserves .current dependsOn derived) ∧
    DependencyCurrent repairedPreserves .current dependsOn derived ∧
    DependencyCurrent preserves .current dependsOn independent ∧
    DependencyCurrent repairedPreserves .current dependsOn independent := by
  refine ⟨derived_invalidated, repaired_bridge_restores_derived,
    independent_current, ?_⟩
  exact dependencyCurrent_mono_preservation
    preserves_extends_to_repaired
    .current dependsOn independent independent_current

end SelectiveCascadeExample

end EvidenceDependency
end DistinctionSelfReference
