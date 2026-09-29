import DistinctionSelfReference.ThreeState

namespace DistinctionSelfReference
namespace KleeneThree

/--
Three truth values for the strong Kleene semantics.

The middle value is intentionally named unknown rather than identified with
Varela's autonomy state; the Varela-to-Kleene syntactic bridge remains a
separate formalization target.
-/
inductive Truth
  | false_
  | unknown
  | true_
  deriving DecidableEq, Repr

/-- Strong Kleene negation. -/
def neg : Truth → Truth
  | .false_ => .true_
  | .unknown => .unknown
  | .true_ => .false_

/-- Strong Kleene disjunction. -/
def disj : Truth → Truth → Truth
  | .true_, _ => .true_
  | _, .true_ => .true_
  | .unknown, _ => .unknown
  | _, .unknown => .unknown
  | .false_, .false_ => .false_

/-- Strong Kleene conjunction. -/
def conj : Truth → Truth → Truth
  | .false_, _ => .false_
  | _, .false_ => .false_
  | .unknown, _ => .unknown
  | _, .unknown => .unknown
  | .true_, .true_ => .true_

theorem neg_involutive : Function.Involutive neg := by
  intro x
  cases x <;> rfl

/-- Unknown is the unique fixed point of strong Kleene negation. -/
theorem neg_fixed_iff_unknown (x : Truth) :
    neg x = x ↔ x = .unknown := by
  cases x <;> simp [neg]

theorem deMorgan_disj (a b : Truth) :
    neg (disj a b) = conj (neg a) (neg b) := by
  cases a <;> cases b <;> rfl

theorem deMorgan_conj (a b : Truth) :
    neg (conj a b) = disj (neg a) (neg b) := by
  cases a <;> cases b <;> rfl

/--
Excluded middle holds exactly on the determined truth values.
The unknown value is therefore the unique obstruction to x ∨ ¬x = true.
-/
theorem excludedMiddle_iff_determined (x : Truth) :
    disj x (neg x) = .true_ ↔ x ≠ .unknown := by
  cases x <;> simp [disj, neg]

/-- Embed ordinary Boolean truth values into the determined K3 values. -/
def ofBool : Bool → Truth
  | false => .false_
  | true => .true_

@[simp] theorem neg_ofBool (b : Bool) :
    neg (ofBool b) = ofBool (Bool.not b) := by
  cases b <;> rfl

@[simp] theorem disj_ofBool (a b : Bool) :
    disj (ofBool a) (ofBool b) = ofBool (a || b) := by
  cases a <;> cases b <;> rfl

@[simp] theorem conj_ofBool (a b : Bool) :
    conj (ofBool a) (ofBool b) = ofBool (a && b) := by
  cases a <;> cases b <;> rfl

/--
The repository's minimal three-state crossing carrier is exactly equivalent,
as a set of states, to the three strong-Kleene truth values.
-/
def stateEquiv : ThreeState.State ≃ Truth where
  toFun
    | .unmarked => .false_
    | .boundary => .unknown
    | .marked => .true_
  invFun
    | .false_ => .unmarked
    | .unknown => .boundary
    | .true_ => .marked
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    intro x
    cases x <;> rfl

/-- Crossing in the three-state model transports exactly to K3 negation. -/
@[simp] theorem stateEquiv_cross (x : ThreeState.State) :
    stateEquiv (ThreeState.cross x) = neg (stateEquiv x) := by
  cases x <;> rfl

@[simp] theorem stateEquiv_boundary :
    stateEquiv ThreeState.State.boundary = .unknown :=
  rfl

/--
The unique static self-reference state of the three-state crossing is the
unique fixed point of strong Kleene negation under the equivalence.
-/
theorem crossing_fixed_iff_unknown (x : ThreeState.State) :
    ThreeState.cross x = x ↔ stateEquiv x = .unknown := by
  rw [ThreeState.fixed_iff_boundary]
  cases x <;> simp [stateEquiv]

end KleeneThree
end DistinctionSelfReference
