import SpringerLean.Round29ComparisonFar

namespace SpringerLean

/-- The actual regularized curve potential minus the comparison segment
potential decays quadratically in the full complex plane. -/
theorem regularExterior_rotated_potential_difference_far_quadratic
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) :
    ∃ R C : ℝ, 0 ≤ R ∧ 0 ≤ C ∧
      ∀ z : ℂ, R < ‖z‖ →
        |regularExteriorRotatedPotential F s ξ z -
          comparisonSegmentPotential z| ≤ C / ‖z‖ ^ 2 := by
  obtain ⟨M, hM0, hactual⟩ :=
    regularExterior_rotated_potential_far_quadratic F hc hs0 hs1 ξ hξ
  let R : ℝ := max (2 * M) 4
  let C : ℝ := M ^ 2 + 4
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨R, C, hR, hC, ?_⟩
  intro z hz
  have hzM : 2 * M < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz
  have hz4 : (4:ℝ) < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hz
  have hA := hactual z hzM
  have hB := comparisonSegmentPotential_far_quadratic z hz4
  have htri := abs_add_le
    (regularExteriorRotatedPotential F s ξ z - Real.log ‖z‖)
    (-(comparisonSegmentPotential z - Real.log ‖z‖))
  have hbound :
      |regularExteriorRotatedPotential F s ξ z - comparisonSegmentPotential z| ≤
        |regularExteriorRotatedPotential F s ξ z - Real.log ‖z‖| +
        |comparisonSegmentPotential z - Real.log ‖z‖| := by
    calc
      |regularExteriorRotatedPotential F s ξ z - comparisonSegmentPotential z| =
          |(regularExteriorRotatedPotential F s ξ z - Real.log ‖z‖) +
            -(comparisonSegmentPotential z - Real.log ‖z‖)| := by ring
      _ ≤ _ := by simpa only [abs_neg] using htri
  have hsum :
      M ^ 2 / ‖z‖ ^ 2 + 4 / ‖z‖ ^ 2 = C / ‖z‖ ^ 2 := by
    dsimp [C]
    ring
  rw [← hsum]
  linarith
end SpringerLean