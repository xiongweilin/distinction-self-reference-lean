import DistinctionSelfReference.ControlSimulation
import DistinctionSelfReference.InformationOrder

namespace DistinctionSelfReference
namespace SafetyInformation

open Viability
open Recovery
open InformationOrder
open ControlSimulation

universe u v w z

/--
An abstraction retains all safety-relevant information when safety is
constant on every fiber of the abstraction map.
-/
def FiberSafeInvariant
    {State : Type u} {Abstract : Type v} {Action : Type w}
    (C : ControlledSystem State Action) (map : State → Abstract) : Prop :=
  ∀ ⦃x y⦄, map x = map y → (x ∈ C.safe ↔ y ∈ C.safe)

/-- The canonical abstract safety set induced by a state abstraction. -/
def inducedSafe
    {State : Type u} {Abstract : Type v} {Action : Type w}
    (C : ControlledSystem State Action) (map : State → Abstract) : Set Abstract :=
  { a | ∃ s, map s = a ∧ s ∈ C.safe }

theorem safe_iff_mem_inducedSafe
    {State : Type u} {Abstract : Type v} {Action : Type w}
    {C : ControlledSystem State Action} {map : State → Abstract}
    (hinv : FiberSafeInvariant C map)
    (s : State) :
    s ∈ C.safe ↔ map s ∈ inducedSafe C map := by
  constructor
  · intro hs
    exact ⟨s, rfl, hs⟩
  · rintro ⟨t, ht, htsafe⟩
    exact (hinv ht).mp htsafe

/--
Safety is fiber-invariant exactly when it factors through some abstract safety
predicate.
-/
theorem fiberSafeInvariant_iff_exists_factor
    {State : Type u} {Abstract : Type v} {Action : Type w}
    (C : ControlledSystem State Action) (map : State → Abstract) :
    FiberSafeInvariant C map ↔
      ∃ safeA : Set Abstract, ∀ s, s ∈ C.safe ↔ map s ∈ safeA := by
  constructor
  · intro hinv
    exact ⟨inducedSafe C map, safe_iff_mem_inducedSafe hinv⟩
  · rintro ⟨safeA, hfactor⟩
    intro x y hxy
    constructor
    · intro hx
      have hxA := (hfactor x).mp hx
      apply (hfactor y).mpr
      simpa [hxy] using hxA
    · intro hy
      have hyA := (hfactor y).mp hy
      apply (hfactor x).mpr
      simpa [hxy] using hyA

/-- Boolean encoding of the safety predicate, when safety is decidable. -/
def safeBit
    {State : Type u} {Action : Type w} (C : ControlledSystem State Action)
    [DecidablePred (fun s => s ∈ C.safe)] : State → Bool :=
  fun s => decide (s ∈ C.safe)

/--
Information-theoretic form: safety is fiber-invariant exactly when the safety
bit is obtainable by deterministic post-processing of the abstraction.
-/
theorem fiberSafeInvariant_iff_refines_safeBit
    {State : Type u} {Abstract : Type v} {Action : Type w}
    (C : ControlledSystem State Action)
    (map : State → Abstract)
    [DecidablePred (fun s => s ∈ C.safe)] :
    FiberSafeInvariant C map ↔ Refines map (safeBit C) := by
  classical
  constructor
  · intro hinv
    let post : Abstract → Bool := fun a => decide (a ∈ inducedSafe C map)
    refine ⟨post, ?_⟩
    funext s
    simp only [safeBit, Function.comp_apply, post]
    have hiff := safe_iff_mem_inducedSafe hinv s
    by_cases hs : s ∈ C.safe
    · have hi : map s ∈ inducedSafe C map := hiff.mp hs
      simp [hs, hi]
    · have hi : map s ∉ inducedSafe C map := by
        intro hmem
        exact hs (hiff.mpr hmem)
      simp [hs, hi]
  · intro href x y hxy
    have hbit : safeBit C x = safeBit C y :=
      equality_preserved_by_postprocessing href hxy
    constructor
    · intro hx
      have hxbit : safeBit C x = true := by
        simp [safeBit, hx]
      have hybit : safeBit C y = true := by
        rw [← hbit]
        exact hxbit
      simpa [safeBit] using hybit
    · intro hy
      have hybit : safeBit C y = true := by
        simp [safeBit, hy]
      have hxbit : safeBit C x = true := by
        rw [hbit]
        exact hybit
      simpa [safeBit] using hxbit

namespace StateMap

variable
  {Concrete : Type u} {Abstract : Type v}
  {ConcreteAction : Type w} {AbstractAction : Type z}
  {C : ControlledSystem Concrete ConcreteAction}
  {A : ControlledSystem Abstract AbstractAction}

/--
If the abstract safe set is the one induced by a safety-sufficient state map,
then safety preservation is automatic.
-/
theorem safePreserving_of_inducedSafe
    (h : StateMap C A)
    (hinv : FiberSafeInvariant C h.map)
    (hsafe : A.safe = inducedSafe C h.map) :
    h.SafePreserving := by
  intro s hs
  rw [hsafe]
  exact (safe_iff_mem_inducedSafe hinv s).mp hs

/-- Under the same information condition, safety reflection is automatic. -/
theorem safeReflecting_of_inducedSafe
    (h : StateMap C A)
    (hinv : FiberSafeInvariant C h.map)
    (hsafe : A.safe = inducedSafe C h.map) :
    h.SafeReflecting := by
  intro s hs
  rw [hsafe] at hs
  exact (safe_iff_mem_inducedSafe hinv s).mpr hs

/--
Forward/backward simulations plus safety-sufficient information give exact
viability, without separately assuming safety preservation/reflection.
-/
theorem mem_kernel_iff_of_safety_information
    (h : StateMap C A)
    (hfwd : h.ForwardSimulates)
    (hbwd : h.BackwardSimulates)
    (hinv : FiberSafeInvariant C h.map)
    (hsafe : A.safe = inducedSafe C h.map)
    (s : Concrete) :
    s ∈ C.kernel ↔ h.map s ∈ A.kernel := by
  have hpres := safePreserving_of_inducedSafe h hinv hsafe
  have hrefl := safeReflecting_of_inducedSafe h hinv hsafe
  constructor
  · exact h.map_kernel_of_forward hfwd hpres
  · exact h.mem_kernel_of_map_mem_kernel_of_backward hbwd hrefl

/-- The same information sufficiency gives exact recoverability. -/
theorem recoverable_iff_of_safety_information
    (h : StateMap C A)
    (hfwd : h.ForwardSimulates)
    (hbwd : h.BackwardSimulates)
    (hinv : FiberSafeInvariant C h.map)
    (hsafe : A.safe = inducedSafe C h.map)
    (s : Concrete) :
    Recoverable C s ↔ Recoverable A (h.map s) := by
  have hpres := safePreserving_of_inducedSafe h hinv hsafe
  have hrefl := safeReflecting_of_inducedSafe h hinv hsafe
  constructor
  · exact h.map_recoverable_of_forward hfwd hpres
  · exact h.recoverable_of_map_recoverable_of_backward hbwd hrefl

end StateMap

/-- The earlier good/bad collapse fails exactly this safety-information test. -/
theorem collapse_not_fiberSafeInvariant :
    ¬ FiberSafeInvariant ControlAbstraction.concrete
      ControlAbstraction.collapse.map := by
  intro hinv
  have hfiber := hinv
    (x := ControlAbstraction.ConcreteState.good)
    (y := ControlAbstraction.ConcreteState.bad)
    rfl
  have hgood :
      ControlAbstraction.ConcreteState.good ∈ ControlAbstraction.concrete.safe :=
    True.intro
  have hbad :
      ControlAbstraction.ConcreteState.bad ∈ ControlAbstraction.concrete.safe :=
    hfiber.mp hgood
  exact hbad

end SafetyInformation
end DistinctionSelfReference
