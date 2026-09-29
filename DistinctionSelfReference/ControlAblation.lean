import DistinctionSelfReference.SafetyInformation

namespace DistinctionSelfReference
namespace ControlAblation

open Viability
open Recovery
open ControlSimulation

/-! ## Forward direction: simulation and safety preservation are independent. -/

/-- One safe self-looping state. -/
def safeUnit : ControlledSystem Unit Unit where
  step _ _ := Unit.unit
  safe _ := True

/-- One unsafe self-looping state. -/
def unsafeUnit : ControlledSystem Unit Unit where
  step _ _ := Unit.unit
  safe _ := False

def safeToUnsafe : StateMap safeUnit unsafeUnit where
  map _ := Unit.unit

theorem safeToUnsafe_forward :
    safeToUnsafe.ForwardSimulates := by
  intro s a
  exact ⟨Unit.unit, rfl⟩

theorem safeToUnsafe_not_safePreserving :
    ¬ safeToUnsafe.SafePreserving := by
  intro h
  exact h (s := Unit.unit) True.intro

theorem safeUnit_viable :
    Unit.unit ∈ safeUnit.kernel := by
  let X : Set Unit := Set.univ
  have hpost : X ⊆ safeUnit.viabilityStep X := by
    intro s hs
    exact ⟨True.intro, Unit.unit, Set.mem_univ _⟩
  exact safeUnit.subset_kernel_of_postfixed X hpost (Set.mem_univ _)

theorem unsafeUnit_not_viable :
    Unit.unit ∉ unsafeUnit.kernel := by
  intro h
  have hs := unsafeUnit.kernel_subset_safe h
  exact hs

theorem unsafeUnit_not_recoverable :
    ¬ Recoverable unsafeUnit Unit.unit := by
  rintro ⟨plan, hplan⟩
  have hrun : run unsafeUnit Unit.unit plan = Unit.unit := by
    induction plan with
    | nil => rfl
    | cons a plan ih => simpa [unsafeUnit] using ih
  rw [hrun] at hplan
  exact unsafeUnit_not_viable hplan

/-- Forward simulation alone does not preserve viability or recoverability. -/
theorem forward_without_safety_is_insufficient :
    safeToUnsafe.ForwardSimulates ∧
      Unit.unit ∈ safeUnit.kernel ∧
      Unit.unit ∉ unsafeUnit.kernel ∧
      Recoverable safeUnit Unit.unit ∧
      ¬ Recoverable unsafeUnit Unit.unit := by
  exact ⟨safeToUnsafe_forward, safeUnit_viable, unsafeUnit_not_viable,
    recoverable_of_mem_kernel safeUnit safeUnit_viable,
    unsafeUnit_not_recoverable⟩

/-- A two-state abstract system whose only action leaves the safe state. -/
def degrading : ControlledSystem Bool Unit where
  step _ _ := false
  safe b := b = true

def safeUnitToDegrading : StateMap safeUnit degrading where
  map _ := true

theorem safeUnitToDegrading_safePreserving :
    safeUnitToDegrading.SafePreserving := by
  intro s hs
  rfl

theorem safeUnitToDegrading_not_forward :
    ¬ safeUnitToDegrading.ForwardSimulates := by
  intro h
  rcases h Unit.unit Unit.unit with ⟨b, hb⟩
  cases b
  change true = false at hb
  exact Bool.true_eq_false_eq_False hb

theorem degrading_false_not_viable :
    false ∉ degrading.kernel := by
  intro h
  have hs := degrading.kernel_subset_safe h
  change false = true at hs
  exact Bool.false_eq_true_eq_False hs

theorem degrading_true_not_viable :
    true ∉ degrading.kernel := by
  intro h
  rcases degrading.viable_has_viable_action h with ⟨a, hnext⟩
  cases a
  have hs := degrading.kernel_subset_safe hnext
  change false = true at hs
  exact Bool.false_eq_true_eq_False hs

theorem degrading_kernel_empty (b : Bool) :
    b ∉ degrading.kernel := by
  cases b
  · exact degrading_false_not_viable
  · exact degrading_true_not_viable

theorem degrading_true_not_recoverable :
    ¬ Recoverable degrading true := by
  rintro ⟨plan, hplan⟩
  exact degrading_kernel_empty (run degrading true plan) hplan

/-- Safety preservation alone does not preserve viability or recoverability. -/
theorem safety_without_forward_is_insufficient :
    safeUnitToDegrading.SafePreserving ∧
      ¬ safeUnitToDegrading.ForwardSimulates ∧
      Unit.unit ∈ safeUnit.kernel ∧
      true ∉ degrading.kernel ∧
      ¬ Recoverable degrading true := by
  exact ⟨safeUnitToDegrading_safePreserving,
    safeUnitToDegrading_not_forward, safeUnit_viable,
    degrading_true_not_viable, degrading_true_not_recoverable⟩

/-! ## Backward direction: simulation and safety reflection are independent. -/

/-- The existing good/bad collapse has backward simulation but loses safety reflection. -/
def collapseMap :
    StateMap ControlAbstraction.concrete ControlAbstraction.abstract :=
  FromHom.stateMap ControlAbstraction.collapse

theorem collapseMap_backward :
    collapseMap.BackwardSimulates :=
  FromHom.backward ControlAbstraction.collapse

theorem collapseMap_not_safeReflecting :
    ¬ collapseMap.SafeReflecting := by
  intro h
  exact h (s := ControlAbstraction.ConcreteState.bad) True.intro

/-- Backward simulation alone does not reflect viability or recoverability. -/
theorem backward_without_reflection_is_insufficient :
    collapseMap.BackwardSimulates ∧
      ¬ collapseMap.SafeReflecting ∧
      Unit.unit ∈ ControlAbstraction.abstract.kernel ∧
      ControlAbstraction.ConcreteState.bad ∉
        ControlAbstraction.concrete.kernel ∧
      Recoverable ControlAbstraction.abstract Unit.unit ∧
      ¬ Recoverable ControlAbstraction.concrete
        ControlAbstraction.ConcreteState.bad := by
  exact ⟨collapseMap_backward, collapseMap_not_safeReflecting,
    ControlAbstraction.abstract_viable, ControlAbstraction.bad_not_viable,
    ControlAbstraction.abstract_recoverable,
    ControlAbstraction.bad_not_recoverable⟩

/-- Same safe predicate as degrading, but the abstract transition stays put. -/
def stableBool : ControlledSystem Bool Unit where
  step b _ := b
  safe b := b = true

def degradingToStable : StateMap degrading stableBool where
  map b := b

theorem degradingToStable_safeReflecting :
    degradingToStable.SafeReflecting := by
  intro s hs
  exact hs

theorem degradingToStable_not_backward :
    ¬ degradingToStable.BackwardSimulates := by
  intro h
  rcases h true Unit.unit with ⟨a, ha⟩
  cases a
  change false = true at ha
  exact Bool.false_eq_true_eq_False ha

theorem stableBool_true_viable :
    true ∈ stableBool.kernel := by
  let X : Set Bool := { b | b = true }
  have hpost : X ⊆ stableBool.viabilityStep X := by
    intro b hb
    change b = true at hb
    subst b
    exact ⟨rfl, Unit.unit, rfl⟩
  exact stableBool.subset_kernel_of_postfixed X hpost rfl

theorem stableBool_true_recoverable :
    Recoverable stableBool true :=
  recoverable_of_mem_kernel stableBool stableBool_true_viable

/-- Safety reflection alone does not reflect viability or recoverability. -/
theorem reflection_without_backward_is_insufficient :
    degradingToStable.SafeReflecting ∧
      ¬ degradingToStable.BackwardSimulates ∧
      true ∈ stableBool.kernel ∧
      true ∉ degrading.kernel ∧
      Recoverable stableBool true ∧
      ¬ Recoverable degrading true := by
  exact ⟨degradingToStable_safeReflecting,
    degradingToStable_not_backward, stableBool_true_viable,
    degrading_true_not_viable, stableBool_true_recoverable,
    degrading_true_not_recoverable⟩

end ControlAblation
end DistinctionSelfReference
