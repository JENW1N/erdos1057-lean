import WeakActualRawBlocks

/-! The exact Erdős 1057 target follows once the selected central moments are proved. -/

namespace Bounty.WeakZeroFree

theorem target_of_selected_central_moments
    (hmoment : ∀ (c : ℝ) (r : ℕ), 0 < c → 6 ≤ r → (11/5 : ℝ) * (r : ℝ) * c = 1 →
      ∀ bWindow : ℝ, 0 < bWindow → CandidateSelectedCentralMoments c bWindow r) :
    fcTypeOfName% "Erdos1057.erdos_1057" := by
  exact target_of_actual_zero_free_and_candidate_half_active_blocks
    (actual_candidate_half_active_blocks_of_selected_central_moments hmoment)

end Bounty.WeakZeroFree
