import SixBirdsMetaMath
import Lean

open Lean Elab Command in
run_elab do
  let env ← getEnv
  let mut count := 0
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "SixBirdsMetaMath." then
      match info with
      | .axiomInfo _ =>
        logInfo m!"Project axiom: {name}"
        count := count + 1
      | _ => pure ()
  logInfo m!"SixBirdsMetaMath project axioms in the imported library: {count}"
  if count != 0 then
    throwError "Project axiom scan failed"
