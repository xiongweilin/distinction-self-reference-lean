import DistinctionSelfReference.EvaluatorProvenance

namespace DistinctionSelfReference
namespace EvaluatorMorphisms

open ChangingEvaluator
open EvaluatorProvenance

universe u v w

/--
A proof-carrying bridge certificate for transporting evaluator semantics along
an explicit state map.

The certificate carries two obligations:
1. every source judgment maps to a target judgment;
2. the fixed external goal is preserved by the state map.
-/
structure BridgeCertificate
    {SourceState : Type u} {TargetState : Type v}
    (source : Evaluator SourceState)
    (target : Evaluator TargetState)
    (mapState : SourceState → TargetState)
    (sourceGoal : SourceState → Nat)
    (targetGoal : TargetState → Nat) : Type (max u v) where
  preservesJudgment :
    ∀ {a b},
      source.better a b →
      target.better (mapState a) (mapState b)
  preservesGoal :
    ∀ s, targetGoal (mapState s) = sourceGoal s

namespace BridgeCertificate

def identity
    {State : Type u}
    (evaluator : Evaluator State)
    (goal : State → Nat) :
    BridgeCertificate evaluator evaluator id goal goal where
  preservesJudgment := fun h => h
  preservesGoal := fun _ => rfl

def comp
    {State₀ : Type u} {State₁ : Type v} {State₂ : Type w}
    {e₀ : Evaluator State₀} {e₁ : Evaluator State₁}
    {e₂ : Evaluator State₂}
    {goal₀ : State₀ → Nat} {goal₁ : State₁ → Nat}
    {goal₂ : State₂ → Nat}
    {f : State₀ → State₁} {g : State₁ → State₂}
    (c₀₁ : BridgeCertificate e₀ e₁ f goal₀ goal₁)
    (c₁₂ : BridgeCertificate e₁ e₂ g goal₁ goal₂) :
    BridgeCertificate e₀ e₂ (g ∘ f) goal₀ goal₂ where
  preservesJudgment := fun h =>
    c₁₂.preservesJudgment (c₀₁.preservesJudgment h)
  preservesGoal := fun s =>
    (c₁₂.preservesGoal (f s)).trans (c₀₁.preservesGoal s)

end BridgeCertificate

/--
A morphism consists of an explicit state translation together with a
checkable preservation certificate.
-/
structure EvaluatorMorphism
    {SourceState : Type u} {TargetState : Type v}
    (source : Evaluator SourceState)
    (target : Evaluator TargetState)
    (sourceGoal : SourceState → Nat)
    (targetGoal : TargetState → Nat) : Type (max u v) where
  mapState : SourceState → TargetState
  certificate :
    BridgeCertificate source target mapState sourceGoal targetGoal

namespace EvaluatorMorphism

theorem mapJudgment
    {SourceState : Type u} {TargetState : Type v}
    {source : Evaluator SourceState}
    {target : Evaluator TargetState}
    {sourceGoal : SourceState → Nat}
    {targetGoal : TargetState → Nat}
    (m : EvaluatorMorphism source target sourceGoal targetGoal)
    {a b : SourceState}
    (h : source.better a b) :
    target.better (m.mapState a) (m.mapState b) :=
  m.certificate.preservesJudgment h

theorem mapGoal
    {SourceState : Type u} {TargetState : Type v}
    {source : Evaluator SourceState}
    {target : Evaluator TargetState}
    {sourceGoal : SourceState → Nat}
    {targetGoal : TargetState → Nat}
    (m : EvaluatorMorphism source target sourceGoal targetGoal)
    (s : SourceState) :
    targetGoal (m.mapState s) = sourceGoal s :=
  m.certificate.preservesGoal s

def identity
    {State : Type u}
    (evaluator : Evaluator State)
    (goal : State → Nat) :
    EvaluatorMorphism evaluator evaluator goal goal where
  mapState := id
  certificate := BridgeCertificate.identity evaluator goal

def comp
    {State₀ : Type u} {State₁ : Type v} {State₂ : Type w}
    {e₀ : Evaluator State₀} {e₁ : Evaluator State₁}
    {e₂ : Evaluator State₂}
    {goal₀ : State₀ → Nat} {goal₁ : State₁ → Nat}
    {goal₂ : State₂ → Nat}
    (m₀₁ : EvaluatorMorphism e₀ e₁ goal₀ goal₁)
    (m₁₂ : EvaluatorMorphism e₁ e₂ goal₁ goal₂) :
    EvaluatorMorphism e₀ e₂ goal₀ goal₂ where
  mapState := m₁₂.mapState ∘ m₀₁.mapState
  certificate :=
    BridgeCertificate.comp m₀₁.certificate m₁₂.certificate

@[simp] theorem identity_mapState
    {State : Type u}
    (evaluator : Evaluator State)
    (goal : State → Nat)
    (s : State) :
    (identity evaluator goal).mapState s = s :=
  rfl

@[simp] theorem comp_mapState
    {State₀ : Type u} {State₁ : Type v} {State₂ : Type w}
    {e₀ : Evaluator State₀} {e₁ : Evaluator State₁}
    {e₂ : Evaluator State₂}
    {goal₀ : State₀ → Nat} {goal₁ : State₁ → Nat}
    {goal₂ : State₂ → Nat}
    (m₀₁ : EvaluatorMorphism e₀ e₁ goal₀ goal₁)
    (m₁₂ : EvaluatorMorphism e₁ e₂ goal₁ goal₂)
    (s : State₀) :
    (comp m₀₁ m₁₂).mapState s =
      m₁₂.mapState (m₀₁.mapState s) :=
  rfl

end EvaluatorMorphism

/--
A version bridge is the same-state specialization used by the provenance
layer. It explicitly certifies identity-state transport between evaluator
versions.
-/
structure VersionBridge
    {Version : Type u} {State : Type v}
    (evaluators : Version → Evaluator State)
    (goal : State → Nat)
    (old new : Version) : Type (max u v) where
  certificate :
    BridgeCertificate
      (evaluators old) (evaluators new) id goal goal

namespace VersionBridge

def identity
    {Version : Type u} {State : Type v}
    (evaluators : Version → Evaluator State)
    (goal : State → Nat)
    (version : Version) :
    VersionBridge evaluators goal version version where
  certificate := BridgeCertificate.identity (evaluators version) goal

def comp
    {Version : Type u} {State : Type v}
    (evaluators : Version → Evaluator State)
    (goal : State → Nat)
    {v₀ v₁ v₂ : Version}
    (b₀₁ : VersionBridge evaluators goal v₀ v₁)
    (b₁₂ : VersionBridge evaluators goal v₁ v₂) :
    VersionBridge evaluators goal v₀ v₂ where
  certificate := {
    preservesJudgment := fun h =>
      b₁₂.certificate.preservesJudgment
        (b₀₁.certificate.preservesJudgment h)
    preservesGoal := fun _ => rfl
  }

theorem preservesJudgments
    {Version : Type u} {State : Type v}
    (evaluators : Version → Evaluator State)
    (goal : State → Nat)
    {old new : Version}
    (bridge : VersionBridge evaluators goal old new) :
    PreservesJudgments evaluators old new := by
  intro a b hab
  exact bridge.certificate.preservesJudgment hab

def ofPreservesJudgments
    {Version : Type u} {State : Type v}
    (evaluators : Version → Evaluator State)
    (goal : State → Nat)
    {old new : Version}
    (h : PreservesJudgments evaluators old new) :
    VersionBridge evaluators goal old new where
  certificate := {
    preservesJudgment := fun {a b} hab => by
      simpa using h a b hab
    preservesGoal := fun _ => rfl
  }

end VersionBridge

/-- Existence of an explicit bridge certificate, used as a provenance policy. -/
def HasVersionBridge
    {Version : Type u} {State : Type v}
    (evaluators : Version → Evaluator State)
    (goal : State → Nat)
    (old new : Version) : Prop :=
  Nonempty (VersionBridge evaluators goal old new)

theorem hasVersionBridge_refl
    {Version : Type u} {State : Type v}
    (evaluators : Version → Evaluator State)
    (goal : State → Nat)
    (version : Version) :
    HasVersionBridge evaluators goal version version :=
  ⟨VersionBridge.identity evaluators goal version⟩

theorem hasVersionBridge_trans
    {Version : Type u} {State : Type v}
    (evaluators : Version → Evaluator State)
    (goal : State → Nat)
    {v₀ v₁ v₂ : Version}
    (h₀₁ : HasVersionBridge evaluators goal v₀ v₁)
    (h₁₂ : HasVersionBridge evaluators goal v₁ v₂) :
    HasVersionBridge evaluators goal v₀ v₂ := by
  rcases h₀₁ with ⟨b₀₁⟩
  rcases h₁₂ with ⟨b₁₂⟩
  exact ⟨VersionBridge.comp evaluators goal b₀₁ b₁₂⟩

end EvaluatorMorphisms
end DistinctionSelfReference
