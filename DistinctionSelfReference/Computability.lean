import Mathlib.Computability.PartrecCode

namespace DistinctionSelfReference
namespace Computability

open Nat.Partrec
open Nat.Partrec.Code

/--
Rogers' fixed-point theorem, reused from Mathlib:
every computable transformation of program codes has an extensional fixed point.
-/
theorem computable_code_transform_has_fixed_point
    {f : Code → Code} (hf : Computable f) :
    ∃ c : Code, eval (f c) = eval c :=
  fixed_point hf

/--
Kleene's second recursion theorem, reused from Mathlib:
a partial-recursive program generator has a code whose behavior is exactly
the behavior generated from its own code.
-/
theorem self_program_exists
    {f : Code → ℕ →. ℕ} (hf : Partrec₂ f) :
    ∃ c : Code, eval c = f c :=
  fixed_point₂ hf

end Computability
end DistinctionSelfReference
