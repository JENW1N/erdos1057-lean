import Challenge
import Lean.Util.CollectAxioms

example : fcTypeOfName% "Erdos1057.erdos_1057" := Bounty.target
example : True ↔ Filter.Tendsto
    (fun x => Real.log (Erdos1057.carmichaelCounting x) / Real.log x)
    Filter.atTop (nhds 1) := Bounty.target

open Lean Elab Command in
run_cmd do
  let axioms ← collectAxioms `Bounty.target
  for axiomName in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
      throwError "Unexpected axiom {axiomName}"

#print axioms Bounty.target
#check @Bounty.target
