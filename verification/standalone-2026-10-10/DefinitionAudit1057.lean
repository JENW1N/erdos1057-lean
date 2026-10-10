import FormalConjectures.ErdosProblems.«1057»

/-! Check the trusted task predicate against an explicit composite/Fermat definition. -/
def ExplicitCarmichael (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧
    ∀ b : ℕ, 1 ≤ b → n.Coprime b → Nat.ProbablePrime n b

theorem carmichael_definition_iff (n : ℕ) :
    IsCarmichael n ↔ ExplicitCarmichael n := by
  constructor
  · intro h
    have h1 : n.FermatPsp 1 := h 1 (by omega) (by simp)
    exact ⟨h1.2.2, h1.2.1, fun b hb hc => (h b hb hc).1⟩
  · intro h b hb hc
    exact ⟨h.2.2 b hb hc, h.2.1, h.1⟩

theorem explicit_carmichael_count (x : ℝ) :
    Erdos1057.carmichaelCounting x =
      (({n : ℕ | ExplicitCarmichael n ∧ (n : ℝ) ≤ x}.ncard : ℕ) : ℝ) := by
  simp only [Erdos1057.carmichaelCounting, carmichael_definition_iff]

#check @carmichael_definition_iff
#print carmichael_definition_iff
#print axioms carmichael_definition_iff
#check @explicit_carmichael_count
#print explicit_carmichael_count
#print axioms explicit_carmichael_count
#print Nat.ProbablePrime
#print Nat.FermatPsp
