import DistinctionSelfReference
import Lean

open Lean Elab Command

/--
Print every non-internal declaration in the project's public namespace.
The shell layer sorts and shards this list before invoking leanexport.
-/
run_cmd do
  let env ← getEnv
  for (n, _) in env.constants.toList do
    let s := n.toString
    if s.startsWith "DistinctionSelfReference." && !n.isInternal then
      IO.println s
