import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Equiv.Defs

namespace DistinctionSelfReference
namespace PrimaryBoolean

universe u

/--
A deliberately small "primary-shaped" syntax:
blank, juxtaposition, crossing, and variables.

This is not yet the quotient/equational theory of Spencer-Brown's primary
algebra. It is the syntax on which we can state and verify a Boolean semantics.
-/
inductive Form (Var : Type u)
  | var : Var → Form Var
  | blank : Form Var
  | concat : Form Var → Form Var → Form Var
  | cross : Form Var → Form Var
  deriving DecidableEq, Repr

namespace Form

variable {Var : Type u}

/-- The nullary mark is a crossing of the blank form. -/
def mark : Form Var :=
  .cross .blank

/--
Boolean interpretation using the OR convention:
blank = false, juxtaposition = OR, crossing = NOT.
-/
def eval (ρ : Var → Bool) : Form Var → Bool
  | .var v => ρ v
  | .blank => false
  | .concat a b => eval ρ a || eval ρ b
  | .cross a => Bool.not (eval ρ a)

/-- Semantic equality under all Boolean valuations. -/
def SemEq (a b : Form Var) : Prop :=
  ∀ ρ, eval ρ a = eval ρ b

/-- Derived conjunction by De Morgan duality. -/
def conj (a b : Form Var) : Form Var :=
  .cross (.concat (.cross a) (.cross b))

@[simp] theorem eval_mark (ρ : Var → Bool) :
    eval ρ (mark : Form Var) = true := by
  rfl

@[simp] theorem eval_conj (ρ : Var → Bool) (a b : Form Var) :
    eval ρ (conj a b) = (eval ρ a && eval ρ b) := by
  cases h₁ : eval ρ a <;> cases h₂ : eval ρ b <;>
    simp [conj, eval, h₁, h₂]

/-- Primary-arithmetic calling law, at the level of Boolean semantics. -/
theorem calling : SemEq
    (.concat (mark : Form Var) mark) mark := by
  intro ρ
  rfl

/-- Primary-arithmetic crossing law, at the level of Boolean semantics. -/
theorem crossing : SemEq
    (.cross (mark : Form Var)) .blank := by
  intro ρ
  rfl

/-- Crossing twice is semantically the identity. -/
theorem double_cross (a : Form Var) :
    SemEq (.cross (.cross a)) a := by
  intro ρ
  cases h : eval ρ a <;> simp [eval, h]

/-- A form juxtaposed with its crossing is always marked/true. -/
theorem position (a : Form Var) :
    ∀ ρ, eval ρ (.concat a (.cross a)) = true := by
  intro ρ
  cases h : eval ρ a <;> simp [eval, h]

end Form

/--
A conventional Boolean-expression syntax with the same functionally complete
basis: false, OR, and NOT.
-/
inductive BoolExpr (Var : Type u)
  | var : Var → BoolExpr Var
  | bot : BoolExpr Var
  | or : BoolExpr Var → BoolExpr Var → BoolExpr Var
  | not : BoolExpr Var → BoolExpr Var
  deriving DecidableEq, Repr

namespace BoolExpr

variable {Var : Type u}

def eval (ρ : Var → Bool) : BoolExpr Var → Bool
  | .var v => ρ v
  | .bot => false
  | .or a b => eval ρ a || eval ρ b
  | .not a => Bool.not (eval ρ a)

end BoolExpr

namespace Form

variable {Var : Type u}

/-- Translate a primary-shaped form into conventional Boolean syntax. -/
def toBoolExpr : Form Var → BoolExpr Var
  | .var v => .var v
  | .blank => .bot
  | .concat a b => .or (toBoolExpr a) (toBoolExpr b)
  | .cross a => .not (toBoolExpr a)

/-- Translate conventional Boolean syntax back into primary-shaped syntax. -/
def ofBoolExpr : BoolExpr Var → Form Var
  | .var v => .var v
  | .bot => .blank
  | .or a b => .concat (ofBoolExpr a) (ofBoolExpr b)
  | .not a => .cross (ofBoolExpr a)

@[simp] theorem ofBoolExpr_toBoolExpr (a : Form Var) :
    ofBoolExpr (toBoolExpr a) = a := by
  induction a <;> simp_all [toBoolExpr, ofBoolExpr]

@[simp] theorem toBoolExpr_ofBoolExpr (a : BoolExpr Var) :
    toBoolExpr (ofBoolExpr a) = a := by
  induction a <;> simp_all [toBoolExpr, ofBoolExpr]

/-- The two raw syntaxes are isomorphic for the false/OR/NOT basis. -/
def syntaxEquiv : Equiv (Form Var) (BoolExpr Var) where
  toFun := toBoolExpr
  invFun := ofBoolExpr
  left_inv := ofBoolExpr_toBoolExpr
  right_inv := toBoolExpr_ofBoolExpr

/-- Translation to conventional Boolean syntax preserves valuation semantics. -/
theorem eval_toBoolExpr (ρ : Var → Bool) (a : Form Var) :
    BoolExpr.eval ρ (toBoolExpr a) = eval ρ a := by
  induction a <;> simp_all [toBoolExpr, BoolExpr.eval, eval]

/-- Translation from conventional Boolean syntax preserves valuation semantics. -/
theorem eval_ofBoolExpr (ρ : Var → Bool) (a : BoolExpr Var) :
    eval ρ (ofBoolExpr a) = BoolExpr.eval ρ a := by
  induction a <;> simp_all [ofBoolExpr, BoolExpr.eval, eval]

end Form
end PrimaryBoolean
end DistinctionSelfReference
