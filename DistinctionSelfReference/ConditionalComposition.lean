import DistinctionSelfReference.CompositionalSufficiency
import DistinctionSelfReference.Recovery

namespace DistinctionSelfReference
namespace ConditionalComposition

open CompositionalSufficiency
open LocalSufficiency
open Viability
open Recovery

universe u v w x y a b

/--
A constructive witness for conditional compositional sufficiency at one world
and one current control state. It records a globally decodable commitment,
agreement with every local requirement, and a finite recovery path to
continued viability.
-/
structure Witness
    {Index : Type u} {World : Type v} {Obs : Type w}
    {Var : Type x} {Value : Type y}
    {State : Type a} {Action : Type b}
    (R : LocalRequirement Index World Obs Var Value)
    (C : ControlledSystem State Action)
    (world : World) (state : State) where
  decode : (Index → Obs) → (Var → Value)
  global : Var → Value
  determined : global = decode (R.combinedObservation world)
  respectsLocal : ∀ i z, z ∈ R.scope i → global z = R.required i world z
  recoveryPlan : List Action
  recoveredViable : run C state recoveryPlan ∈ C.kernel

/--
Local sufficiency + overlap compatibility + minimum recoverability construct
a conditional composition witness.
-/
noncomputable def witness_of_localSufficiency_compatibility_recoverability
    {Index : Type u} {World : Type v} {Obs : Type w}
    {Var : Type x} {Value : Type y}
    {State : Type a} {Action : Type b}
    (R : LocalRequirement Index World Obs Var Value)
    (C : ControlledSystem State Action)
    (hcover : R.Covers)
    (hcompat : R.Compatible)
    (hlocal : R.LocallySufficient)
    (world : World) (state : State)
    (hrecover : Recoverable C state) :
    Witness R C world state :=
  let hcompose := R.local_sufficiency_glues_to_global hcover hcompat hlocal
  let hsuff := hcompose.1
  let hextend := hcompose.2
  let decode := Classical.choose hsuff
  let hdecode := Classical.choose_spec hsuff
  let plan := Classical.choose hrecover
  let hplan := Classical.choose_spec hrecover
  {
    decode := decode
    global := R.globalRequired hcover world
    recoveryPlan := plan
    recoveredViable := hplan
    determined := congrFun hdecode world
    respectsLocal := by
      intro i z hz
      exact hextend world i z hz
  }

/--
Every witness exposes the two guarantees separately: epistemic/compositional
determinacy and minimum recoverability.
-/
theorem witness_has_recovery
    {Index : Type u} {World : Type v} {Obs : Type w}
    {Var : Type x} {Value : Type y}
    {State : Type a} {Action : Type b}
    {R : LocalRequirement Index World Obs Var Value}
    {C : ControlledSystem State Action}
    {world : World} {state : State}
    (W : Witness R C world state) :
    Recoverable C state := by
  exact ⟨W.recoveryPlan, W.recoveredViable⟩

end ConditionalComposition
end DistinctionSelfReference
