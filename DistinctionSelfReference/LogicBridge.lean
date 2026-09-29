import DistinctionSelfReference.PrimaryBoolean
import DistinctionSelfReference.KleeneThree

namespace DistinctionSelfReference
namespace LogicBridge

universe u

/--
Interpret the primary-shaped form language in Strong Kleene K3:
blank = false, juxtaposition = K3 disjunction, crossing = K3 negation.
-/
def evalPrimaryK3 {Var : Type u}
    (ρ : Var → KleeneThree.Truth) :
    PrimaryBoolean.Form Var → KleeneThree.Truth
  | .var v => ρ v
  | .blank => .false_
  | .concat a b =>
      KleeneThree.disj (evalPrimaryK3 ρ a) (evalPrimaryK3 ρ b)
  | .cross a =>
      KleeneThree.neg (evalPrimaryK3 ρ a)

/--
K3 conservatively extends the Boolean primary semantics on determined
(Boolean-valued) valuations.
-/
theorem evalPrimaryK3_ofBool
    {Var : Type u}
    (ρ : Var → Bool)
    (a : PrimaryBoolean.Form Var) :
    evalPrimaryK3 (fun v => KleeneThree.ofBool (ρ v)) a =
      KleeneThree.ofBool (PrimaryBoolean.Form.eval ρ a) := by
  induction a <;>
    simp_all [evalPrimaryK3, PrimaryBoolean.Form.eval, KleeneThree.ofBool]

/--
The primary Boolean position/excluded-middle form remains true under every
determined Boolean valuation when embedded into K3.
-/
theorem position_on_boolean_valuations
    {Var : Type u}
    (ρ : Var → Bool)
    (a : PrimaryBoolean.Form Var) :
    evalPrimaryK3 (fun v => KleeneThree.ofBool (ρ v))
      (.concat a (.cross a)) = .true_ := by
  rw [evalPrimaryK3_ofBool]
  rw [PrimaryBoolean.Form.position a ρ]
  rfl

/--
For arbitrary K3 valuations, the position form is true exactly when the
subform has a determined value. Thus the K3 unknown value is precisely the
new obstruction introduced by the three-valued extension.
-/
theorem position_iff_determined
    {Var : Type u}
    (ρ : Var → KleeneThree.Truth)
    (a : PrimaryBoolean.Form Var) :
    evalPrimaryK3 ρ (.concat a (.cross a)) = .true_ ↔
      evalPrimaryK3 ρ a ≠ .unknown := by
  simpa [evalPrimaryK3] using
    KleeneThree.excludedMiddle_iff_determined (evalPrimaryK3 ρ a)

/-- A concrete unknown valuation witnesses failure of Boolean excluded middle. -/
theorem position_unknown_counterexample
    {Var : Type u}
    (v : Var) :
    evalPrimaryK3 (fun _ => KleeneThree.Truth.unknown)
      (.concat (.var v) (.cross (.var v))) =
      KleeneThree.Truth.unknown := by
  rfl

end LogicBridge
end DistinctionSelfReference
