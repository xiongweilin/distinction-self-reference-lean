import DistinctionSelfReference
import Lean

open Lean Elab Command

/--
Print every non-internal declaration in the project's public namespace.
Diagnostics go to stderr so stdout stays machine-readable.
-/
run_cmd do
  let env ← getEnv
  let prefix := Name.mkSimple "DistinctionSelfReference"
  let mut count := 0
  for (n, _) in env.constants.toList do
    if prefix.isPrefixOf n && !n.isInternal then
      IO.println n
      count := count + 1
  IO.eprintln s!"matched project constants: {count}"
  if count == 0 then
    throw <| IO.userError "no DistinctionSelfReference declarations found"
