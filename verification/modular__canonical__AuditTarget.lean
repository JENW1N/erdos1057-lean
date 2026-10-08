import ActualErdos1057Target
import Lean.Util.CollectAxioms

/-! Verify the exact challenge statement and the allowed axiom closure. -/

example : fcTypeOfName% "Erdos1057.erdos_1057" := Bounty.target

open Lean Elab Command in
run_cmd do
  let axioms ← collectAxioms `Bounty.target
  for axiomName in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
      throwError "Unexpected axiom {axiomName}"

#print axioms Bounty.target
#check @Bounty.target
