import SpringerLean.Round29ReferenceBridge

namespace SpringerLean

/-- Both the actual regularized boundary potential and the comparison
segment potential approach the common radial logarithmic reference at
quadratic reciprocal rate. -/
theorem regularExterior_potentials_reference_far_quadratic
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) :
    ∃ R C : ℝ, 0 ≤ R ∧ 0 ≤ C ∧
      ∀ z : ℂ, R < ‖z‖ →
        |regularExteriorRotatedPotential F s ξ z - radialReferencePotential z| +
          |comparisonSegmentPotential z - radialReferencePotential z| ≤
            C / ‖z‖ ^ 2 := by
  obtain ⟨M, hM0, hactual⟩ :=
    regularExterior_rotated_potential_far_quadratic F hc hs0 hs1 ξ hξ
  let R : ℝ := max (2 * M) 4
  let C : ℝ := M ^ 2 + 5
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨R, C, hR, hC, ?_⟩
  intro z hz
  have hzM : 2 * M < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz
  have hz4 : (4:ℝ) < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hz
  have hzn : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hA := hactual z hzM
  have hB := comparisonSegmentPotential_far_quadratic z hz4
  obtain ⟨hRef0, hRef⟩ := radialReferencePotential_sub_log_norm_bound z hzn
  have hTA := abs_add_le
    (regularExteriorRotatedPotential F s ξ z - Real.log ‖z‖)
    (-(radialReferencePotential z - Real.log ‖z‖))
  have hTB := abs_add_le
    (comparisonSegmentPotential z - Real.log ‖z‖)
    (-(radialReferencePotential z - Real.log ‖z‖))
  have ha :
      |regularExteriorRotatedPotential F s ξ z - radialReferencePotential z| ≤
        M ^ 2 / ‖z‖ ^ 2 + (1 / 2 : ℝ) / ‖z‖ ^ 2 := by
    have hrep : regularExteriorRotatedPotential F s ξ z - radialReferencePotential z =
      (regularExteriorRotatedPotential F s ξ z - Real.log ‖z‖) +
      -(radialReferencePotential z - Real.log ‖z‖) := by ring
    rw [hrep]
    have htri := hTA
    rw [abs_neg, abs_of_nonneg hRef0] at htri
    linarith
  have hb :
      |comparisonSegmentPotential z - radialReferencePotential z| ≤
        (4 : ℝ) / ‖z‖ ^ 2 + (1 / 2 : ℝ) / ‖z‖ ^ 2 := by
    have hrep : comparisonSegmentPotential z - radialReferencePotential z =
      (comparisonSegmentPotential z - Real.log ‖z‖) +
      -(radialReferencePotential z - Real.log ‖z‖) := by ring
    rw [hrep]
    have htri := hTB
    rw [abs_neg, abs_of_nonneg hRef0] at htri
    linarith
  have hsum : M ^ 2 / ‖z‖ ^ 2 + (1 / 2 : ℝ) / ‖z‖ ^ 2 +
      ((4 : ℝ) / ‖z‖ ^ 2 + (1 / 2 : ℝ) / ‖z‖ ^ 2) =
      C / ‖z‖ ^ 2 := by dsimp [C]; ring
  rw [← hsum]
  linarith
end SpringerLean