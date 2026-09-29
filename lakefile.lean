import Lake
open Lake DSL

package "distinction-self-reference" where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`pp.unicode.fun, true⟩
  ]

require "leanprover-community" / "mathlib" @ git "344385a8816d926e65be4f6b76c7b3b476d2dde5"

@[default_target]
lean_lib DistinctionSelfReference where
