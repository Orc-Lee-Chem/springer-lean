import SpringerLean.Round1384ShortArcQuadratic

open MeasureTheory

namespace SpringerLean

/-- The two polynomial moments of the uniformly averaged short arc. -/
theorem coarseArc_polynomial_moments (b : ℝ) :
    (∫ θ in (0:ℝ)..b, θ^2) = b^3/3 ∧
      (∫ θ in (0:ℝ)..b, θ^4) = b^5/5 := by
  constructor
  · rw [integral_pow]
    norm_num
  · rw [integral_pow]
    norm_num

/-- One-dimensional variance bound for `S(θ)=2−2cos θ` on the bad-end
arc. No double integral or abstract probability variance is used. -/
theorem coarseArc_deficit_variance_lower
    (n : ℕ) (hn : 1501 ≤ n) :
    let b : ℝ := Real.sqrt (3/(n:ℝ))
    let S : ℝ → ℝ := fun θ => 2-2*Real.cos θ
    (1/b)*(∫ θ in (0:ℝ)..b, S θ^2) -
      ((1/b)*(∫ θ in (0:ℝ)..b, S θ))^2 ≥
      (99/100 : ℝ)*4*b^4/45 := by
  dsimp
  let b : ℝ := Real.sqrt (3/(n:ℝ))
  let S : ℝ → ℝ := fun θ => 2-2*Real.cos θ
  have hb : 0 < b := (coarseArc_mean_bounds n hn).1
  have hb0 : 0 ≤ b := hb.le
  have hIntS : IntervalIntegrable S volume 0 b := by
    apply Continuous.intervalIntegrable
    dsimp [S]; fun_prop
  have hIntSsq : IntervalIntegrable (fun θ : ℝ => S θ^2) volume 0 b := by
    apply Continuous.intervalIntegrable
    dsimp [S]; fun_prop
  have hInt2 : IntervalIntegrable (fun θ : ℝ => θ^2) volume 0 b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hInt4 : IntervalIntegrable (fun θ : ℝ => θ^4) volume 0 b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hS0 : 0 ≤ (1/b)*(∫ θ in (0:ℝ)..b, S θ) := by
    have hnonneg : 0 ≤ ∫ θ in (0:ℝ)..b, S θ := by
      apply intervalIntegral.integral_nonneg hb0
      intro θ hθ
      dsimp [S]
      linarith [Real.cos_le_one θ]
    exact mul_nonneg (by positivity) hnonneg
  have hSupper :
      (1/b)*(∫ θ in (0:ℝ)..b, S θ) ≤ b^2/3 := by
    have hraw : (∫ θ in (0:ℝ)..b, S θ) ≤
        ∫ θ in (0:ℝ)..b, θ^2 := by
      apply intervalIntegral.integral_mono_on hb0 hIntS hInt2
      intro θ hθ
      exact (coarseArc_cos_deficit_quadratic n hn hθ.1 hθ.2).2
    rw [(coarseArc_polynomial_moments b).1] at hraw
    have hnorm := mul_le_mul_of_nonneg_left hraw
      (show 0 ≤ 1/b by positivity)
    have hbne : b ≠ 0 := ne_of_gt hb
    have hpow : (1/b)*(b^3/3)=b^2/3 := by field_simp [hbne]
    rw [hpow] at hnorm
    exact hnorm
  have hSsqLower :
      (999/1000 : ℝ)^2*b^4/5 ≤
        (1/b)*(∫ θ in (0:ℝ)..b, S θ^2) := by
    have hraw :
        (999/1000 : ℝ)^2 * (∫ θ in (0:ℝ)..b, θ^4) ≤
        ∫ θ in (0:ℝ)..b, S θ^2 := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on hb0
      · exact hInt4.const_mul _
      · exact hIntSsq
      intro θ hθ
      have hpoint := (coarseArc_cos_deficit_quadratic n hn hθ.1 hθ.2).1
      have hSpos : 0 ≤ S θ := by dsimp [S]; linarith [Real.cos_le_one θ]
      have hθpos : 0 ≤ (999/1000 : ℝ)*θ^2 := by positivity
      have hproduct := mul_nonneg (sub_nonneg.mpr hpoint)
        (add_nonneg hSpos hθpos)
      dsimp [S] at *
      nlinarith
    rw [(coarseArc_polynomial_moments b).2] at hraw
    have hnorm := mul_le_mul_of_nonneg_left hraw
      (show 0 ≤ 1/b by positivity)
    have hbne : b ≠ 0 := ne_of_gt hb
    have hpow : (1/b)*((999/1000 : ℝ)^2*(b^5/5)) =
        (999/1000 : ℝ)^2*b^4/5 := by field_simp [hbne]
    rw [hpow] at hnorm
    exact hnorm
  have hSmeanSq :
      ((1/b)*(∫ θ in (0:ℝ)..b, S θ))^2 ≤ b^4/9 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hSupper)
      (add_nonneg hS0 (by positivity : 0 ≤ b^2/3))
    nlinarith
  have hb4 : 0 ≤ b^4 := by positivity
  have hnumeric :
      (99/100 : ℝ)*4*b^4/45 ≤
        (999/1000 : ℝ)^2*b^4/5 - b^4/9 := by
    nlinarith
  nlinarith

end SpringerLean

#print axioms SpringerLean.coarseArc_deficit_variance_lower
