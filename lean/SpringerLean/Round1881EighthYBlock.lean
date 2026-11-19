import SpringerLean.Round1880EighthWBlock

namespace SpringerLean

set_option maxHeartbeats 2000000

/-- Three-term weighted Cauchy--Schwarz in the exact weights 6,4,2.
The difference is a sum of three explicit rational squares. -/
theorem eighth_weighted_three_cauchy
    (a b c α γ : ℝ) :
    (a + α * b + γ * c) ^ 2 ≤
      (1 / 6 + α ^ 2 / 4 + γ ^ 2 / 2) *
        (6 * a ^ 2 + 4 * b ^ 2 + 2 * c ^ 2) := by
  nlinarith [sq_nonneg (4 * b - 6 * α * a),
    sq_nonneg (2 * c - 6 * γ * a),
    sq_nonneg (2 * α * c - 4 * γ * b)]

theorem eighth_y_actual_energy_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    4 * ‖exteriorForwardCoeff F 6 +
      3 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 4 +
      3 * (exteriorForwardCoeff F 3 + exteriorForwardCoeff F 1 ^ 2) *
        exteriorForwardCoeff F 2‖ ^ 2 ≤
      (2 / 3 + 9 * ‖exteriorForwardCoeff F 1‖ ^ 2 +
        (9 / 2 : ℝ) * (1 + ‖exteriorForwardCoeff F 1‖ ^ 2) ^ 2) *
        (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) := by
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  let b₃ := exteriorForwardCoeff F 3
  let b₄ := exteriorForwardCoeff F 4
  let b₆ := exteriorForwardCoeff F 6
  let g := b₃ + b₁ ^ 2
  let y := b₆ + 3 * b₁ * b₄ + 3 * g * b₂
  let D := 1 - ‖b₁‖ ^ 2
  let E := 6 * ‖b₆‖ ^ 2 + 4 * ‖b₄‖ ^ 2 + 2 * ‖b₂‖ ^ 2
  let M := (1 / 6 : ℝ) + (3 * ‖b₁‖) ^ 2 / 4 + (3 * ‖g‖) ^ 2 / 2
  have harea := exteriorForwardCoeff_finite_area F hc 6
  have hset : Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by decide
  rw [hset] at harea
  norm_num at harea
  have hbudget : E ≤ D := by
    dsimp only [E, D, b₁, b₂, b₄, b₆]
    nlinarith [sq_nonneg ‖exteriorForwardCoeff F 3‖,
      sq_nonneg ‖exteriorForwardCoeff F 5‖]
  have hD : 0 ≤ D := by
    dsimp only [D, E] at hbudget
    have hE : 0 ≤ 6 * ‖b₆‖ ^ 2 + 4 * ‖b₄‖ ^ 2 + 2 * ‖b₂‖ ^ 2 := by
      positivity
    linarith
  have hginv := exteriorInverseCoeff_three_norm_le_half_one_add_sq F hc
  rw [exteriorInverseCoeff_three_eq_forward F hc] at hginv
  have hg : ‖g‖ ≤ (1 + ‖b₁‖ ^ 2) / 2 := by
    simpa only [g, b₁, b₃] using hginv
  have hgsq : ‖g‖ ^ 2 ≤ ((1 + ‖b₁‖ ^ 2) / 2) ^ 2 := by
    nlinarith [norm_nonneg g]
  have htriangle : ‖y‖ ≤ ‖b₆‖ + 3 * ‖b₁‖ * ‖b₄‖ + 3 * ‖g‖ * ‖b₂‖ := by
    have h1 := norm_add_le b₆ (3 * b₁ * b₄)
    have h2 := norm_add_le (b₆ + 3 * b₁ * b₄) (3 * g * b₂)
    dsimp only [y]
    norm_num [norm_mul] at h1 h2
    nlinarith
  have hysq : ‖y‖ ^ 2 ≤
      (‖b₆‖ + 3 * ‖b₁‖ * ‖b₄‖ + 3 * ‖g‖ * ‖b₂‖) ^ 2 := by
    nlinarith [norm_nonneg y]
  have hcs := eighth_weighted_three_cauchy
    ‖b₆‖ ‖b₄‖ ‖b₂‖ (3 * ‖b₁‖) (3 * ‖g‖)
  have hM : 0 ≤ M := by
    dsimp only [M]
    positivity
  have hstep : ‖y‖ ^ 2 ≤ M * D := by
    have hmul := mul_le_mul_of_nonneg_left hbudget hM
    calc
      ‖y‖ ^ 2 ≤
          (‖b₆‖ + 3 * ‖b₁‖ * ‖b₄‖ + 3 * ‖g‖ * ‖b₂‖) ^ 2 := hysq
      _ ≤ M * E := hcs
      _ ≤ M * D := hmul
  have hMbound : 4 * M ≤
      2 / 3 + 9 * ‖b₁‖ ^ 2 + (9 / 2 : ℝ) * (1 + ‖b₁‖ ^ 2) ^ 2 := by
    dsimp only [M]
    nlinarith
  have hfinal := mul_le_mul_of_nonneg_right hMbound hD
  dsimp only [M, D, y, g, b₁, b₂, b₃, b₄, b₆] at hstep hfinal
  nlinarith

end SpringerLean
