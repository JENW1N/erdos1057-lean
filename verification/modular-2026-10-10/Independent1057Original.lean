import ActualErdos1057Target

open Filter
open scoped Topology

def Intended1057 : Prop :=
  Tendsto
    (fun x : ℝ =>
      Real.log (({n : ℕ | _root_.IsCarmichael n ∧ (n : ℝ) ≤ x}.ncard : ℝ)) /
        Real.log x)
    atTop (nhds 1)

theorem checked1057Original : Intended1057 := by
  simpa only [Intended1057, Erdos1057.carmichaelCounting] using
    (Bounty.target.mp True.intro)

#check @Bounty.target
#print Bounty.target
#check @checked1057Original
#print checked1057Original
#print axioms checked1057Original
#print axioms Bounty.target
#print Erdos1057.carmichaelCounting
#print IsCarmichael
