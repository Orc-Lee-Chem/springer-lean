import SpringerLean.Round1887InterpolationPowerAMGM

namespace SpringerLean

/-- The interpolation loss is bounded by an affine endpoint loss. -/
theorem interpolation_loss_square_identity (θ : ℝ) :
    4 - 3 * θ - 9 * θ * (1 - θ) = (3 * θ - 2) ^ 2 := by
  ring

theorem interpolation_affine_remainder
    {A B L θ : ℝ} (hL : 0 ≤ L) :
    (1 - θ) * A + θ * B - L * θ * (1 - θ) ≥
      (1 - θ) * (A - 4 * L / 9) + θ * (B - L / 9) := by
  have hs := sq_nonneg (3 * θ - 2)
  nlinarith [interpolation_loss_square_identity θ]

theorem interpolation_four_to_six_strong_margin
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) * (3 / 64 : ℝ) + θ * (7 / 384) -
      (19 / 224) * θ * (1 - θ) ≥ 1 / 640 := by
  have hA : (1 / 640 : ℝ) ≤ 3 / 64 - 4 * (19 / 224) / 9 := by norm_num
  have hB : (1 / 640 : ℝ) ≤ 7 / 384 - (19 / 224) / 9 := by norm_num
  have h := interpolation_affine_remainder
    (A := (3 / 64 : ℝ)) (B := 7 / 384) (L := 19 / 224)
    (θ := θ) (by norm_num)
  nlinarith [mul_nonneg (show 0 ≤ 1 - θ by linarith)
    (sub_nonneg.mpr hA), mul_nonneg hθ0 (sub_nonneg.mpr hB)]

theorem interpolation_six_to_eight_strong_margin
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) * (7 / 384 : ℝ) + θ * (51 / 10240) -
      (13 / 448) * θ * (1 - θ) ≥ 1 / 640 := by
  have hA : (1 / 640 : ℝ) ≤ 7 / 384 - 4 * (13 / 448) / 9 := by norm_num
  have hB : (1 / 640 : ℝ) ≤ 51 / 10240 - (13 / 448) / 9 := by norm_num
  have h := interpolation_affine_remainder
    (A := (7 / 384 : ℝ)) (B := 51 / 10240) (L := 13 / 448)
    (θ := θ) (by norm_num)
  nlinarith [mul_nonneg (show 0 ≤ 1 - θ by linarith)
    (sub_nonneg.mpr hA), mul_nonneg hθ0 (sub_nonneg.mpr hB)]

/-- Algebraic final step after the analytic interpolation inequality has
been established for one actual map. -/
theorem interpolation_from_bracket_to_normalized_deficit
    {p D C M B : ℝ} (hp : 4 ≤ p) (hD : 0 ≤ D)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1 / 2)
    (hB : 1 / 640 ≤ B) (hmain : p * D * B ≤ C - M) :
    M ≤ C * (1 - D / 80) := by
  have hpD : 0 ≤ p * D := mul_nonneg (by linarith) hD
  have h1 := mul_le_mul_of_nonneg_left hB hpD
  have h2 := mul_le_mul_of_nonneg_right hp hD
  have h3 := mul_le_mul_of_nonneg_right hC1 hD
  nlinarith

end SpringerLean

#print axioms SpringerLean.interpolation_four_to_six_strong_margin
#print axioms SpringerLean.interpolation_six_to_eight_strong_margin
