import SpringerLean.SecondTail

open Complex
open scoped ComplexConjugate

namespace SpringerLean

/-- The real-linear correction used on the outer circle. -/
noncomputable def exteriorLinearCorrection
    (F : ℂ → ℂ) (R : ℝ) (w : ℂ) : ℂ :=
  w - (exteriorForwardCoeff F 1 / (R : ℂ) ^ 2) * star w

/-- On |z|=R the conjugate of z is R²/z. -/
theorem circle_conj_eq_radius_sq_mul_inv
    {z : ℂ} {R : ℝ} (hR : 0 < R) (hz : ‖z‖ = R) :
    star z = (R : ℂ) ^ 2 * z⁻¹ := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
    linarith
  have hmul : z * star z = (R : ℂ) ^ 2 := by
    change z * conj z = (R : ℂ) ^ 2
    rw [Complex.mul_conj', hz]
  apply mul_left_cancel₀ hz0
  rw [hmul]
  field_simp [hz0]

theorem circle_first_mode_cancel
    (b z : ℂ) {R : ℝ} (hR : 0 < R) (hz : ‖z‖ = R) :
    (b / (R : ℂ) ^ 2) * star z = b * z⁻¹ := by
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  rw [circle_conj_eq_radius_sq_mul_inv hR hz]
  field_simp [hR0]

/-- Exact cancellation of b₁/z on the outer circle, before estimates. -/
theorem exteriorLinearCorrection_circle_identity
    (F : ℂ → ℂ) {z : ℂ} {R : ℝ}
    (hR : 0 < R) (hz : ‖z‖ = R) :
    exteriorLinearCorrection F R (F z) =
      z + (z⁻¹) ^ 2 * exteriorSecondTail F z⁻¹ -
        (exteriorForwardCoeff F 1 / (R : ℂ) ^ 2) *
          star (F z - z) := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
    linarith
  have hforward := exteriorForwardGerm_eq_first_add_secondTail F z⁻¹
  rw [exteriorForwardGerm_punctured F (inv_ne_zero hz0)] at hforward
  have hF : F z - z =
      exteriorForwardCoeff F 1 * z⁻¹ +
        (z⁻¹) ^ 2 * exteriorSecondTail F z⁻¹ := by
    simpa only [inv_inv] using hforward
  have hconj : star (F z) = star z + star (F z - z) := by
    have h : F z = z + (F z - z) := by ring
    conv_lhs => rw [h]
    simp
  have hcancel := circle_first_mode_cancel
    (exteriorForwardCoeff F 1) z hR hz
  unfold exteriorLinearCorrection
  rw [hconj]
  calc
    F z - (exteriorForwardCoeff F 1 / (R : ℂ) ^ 2) *
        (star z + star (F z - z)) =
      z + (F z - z) -
        (exteriorForwardCoeff F 1 / (R : ℂ) ^ 2) * star z -
        (exteriorForwardCoeff F 1 / (R : ℂ) ^ 2) * star (F z - z) := by ring
    _ = z + (z⁻¹) ^ 2 * exteriorSecondTail F z⁻¹ -
        (exteriorForwardCoeff F 1 / (R : ℂ) ^ 2) * star (F z - z) := by
          rw [hF, hcancel]
          ring

/-- Explicit bound after cancellation of the first negative mode. -/
theorem exteriorLinearCorrection_circle_norm_bound
    (F : ℂ → ℂ) {z : ℂ} {R C : ℝ}
    (hR : 0 < R) (hz : ‖z‖ = R)
    (hT : ‖exteriorSecondTail F z⁻¹‖ ≤ C) :
    ‖exteriorLinearCorrection F R (F z)‖ ≤
      R + C / R ^ 2 +
        (‖exteriorForwardCoeff F 1‖ / R ^ 2) *
          (‖exteriorForwardCoeff F 1‖ / R + C / R ^ 2) := by
  let b := exteriorForwardCoeff F 1
  let T := exteriorSecondTail F z⁻¹
  have hz0 : z ≠ 0 := by
    intro heq
    simp [heq] at hz
    linarith
  have hInv : ‖z⁻¹‖ = R⁻¹ := by rw [norm_inv, hz]
  have hF : F z - z = b * z⁻¹ + (z⁻¹) ^ 2 * T := by
    have hf := exteriorForwardGerm_eq_first_add_secondTail F z⁻¹
    rw [exteriorForwardGerm_punctured F (inv_ne_zero hz0)] at hf
    simpa only [inv_inv] using hf
  have hFnorm : ‖F z - z‖ ≤ ‖b‖ / R + C / R ^ 2 := by
    rw [hF]
    calc
      ‖b * z⁻¹ + (z⁻¹) ^ 2 * T‖ ≤
          ‖b‖ * ‖z⁻¹‖ + ‖z⁻¹‖ ^ 2 * ‖T‖ := by
            calc
              _ ≤ ‖b * z⁻¹‖ + ‖(z⁻¹) ^ 2 * T‖ := norm_add_le _ _
              _ = _ := by rw [norm_mul, norm_mul, norm_pow]
      _ ≤ ‖b‖ / R + C / R ^ 2 := by
        rw [hInv]
        have hnonneg : 0 ≤ (R⁻¹) ^ 2 := sq_nonneg _
        calc
          ‖b‖ * R⁻¹ + (R⁻¹) ^ 2 * ‖T‖ ≤
              ‖b‖ * R⁻¹ + (R⁻¹) ^ 2 * C := by
                exact add_le_add (le_refl _)
                  (mul_le_mul_of_nonneg_left hT hnonneg)
          _ = ‖b‖ / R + C / R ^ 2 := by
            field_simp
  rw [exteriorLinearCorrection_circle_identity F hR hz]
  calc
    ‖z + (z⁻¹) ^ 2 * T - (b / (R : ℂ) ^ 2) * star (F z - z)‖ ≤
        ‖z‖ + ‖(z⁻¹) ^ 2 * T‖ +
          ‖(b / (R : ℂ) ^ 2) * star (F z - z)‖ := by
            have h1 := norm_sub_le
              (z + (z⁻¹) ^ 2 * T)
              ((b / (R : ℂ) ^ 2) * star (F z - z))
            have h2 := norm_add_le z ((z⁻¹) ^ 2 * T)
            linarith
    _ ≤ R + C / R ^ 2 + (‖b‖ / R ^ 2) *
        (‖b‖ / R + C / R ^ 2) := by
      rw [hz, norm_mul, norm_pow, hInv, norm_mul, norm_star, norm_div,
        norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
      have h2 : 0 ≤ R⁻¹ ^ 2 := sq_nonneg _
      have h3 : 0 ≤ ‖b‖ / R ^ 2 := div_nonneg (norm_nonneg _) (sq_nonneg _)
      have hT' : (R⁻¹)^2 * ‖T‖ ≤ C / R^2 := by
        calc
          _ ≤ (R⁻¹)^2 * C := mul_le_mul_of_nonneg_left hT h2
          _ = C / R^2 := by field_simp
      have hM' : (‖b‖ / R^2) * ‖F z - z‖ ≤
          (‖b‖ / R^2) * (‖b‖ / R + C / R^2) :=
        mul_le_mul_of_nonneg_left hFnorm h3
      nlinarith

/-- The explicit outer-circle bound holds uniformly once the reciprocal
radius lies in the analytic neighborhood of infinity. -/
theorem exteriorLinearCorrection_large_circle_norm_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (R : ℝ) (z : ℂ), 0 < R → ‖z‖ = R → R⁻¹ < δ →
        ‖exteriorLinearCorrection F R (F z)‖ ≤
          R + (‖exteriorSecondTail F 0‖ + 1) / R ^ 2 +
            (‖exteriorForwardCoeff F 1‖ / R ^ 2) *
              (‖exteriorForwardCoeff F 1‖ / R +
                (‖exteriorSecondTail F 0‖ + 1) / R ^ 2) := by
  obtain ⟨δ, hδ, htail⟩ := Metric.eventually_nhds_iff.mp
    (exteriorSecondTail_eventually_norm_bound F hc)
  refine ⟨δ, hδ, ?_⟩
  intro R z hR hz hsmall
  apply exteriorLinearCorrection_circle_norm_bound F hR hz
  apply htail
  simpa only [dist_zero_right, norm_inv, hz] using hsmall

end SpringerLean
