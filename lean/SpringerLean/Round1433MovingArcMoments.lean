import SpringerLean.Round1432MovingArcMean
import SpringerLean.Round1385ArcVariance

open MeasureTheory

namespace SpringerLean
set_option maxHeartbeats 200000

/-- Uniform quadratic approximation to the cosine deficit on any
moving arc shorter than `1/20`. -/
theorem movingArc_cos_deficit_quadratic
    {b θ : ℝ} (hb : b ≤ 1/20)
    (hθ0 : 0 ≤ θ) (hθb : θ ≤ b) :
    (999/1000:ℝ)*θ^2 ≤ 2-2*Real.cos θ ∧
      2-2*Real.cos θ ≤ θ^2 := by
  have hθsmall : θ ≤ 1/20 := hθb.trans hb
  have hθsq : θ^2 ≤ 1/400 := by
    nlinarith [sq_nonneg (θ-1/20)]
  have hθfour : θ^4 ≤ θ^2/400 := by
    nlinarith [mul_nonneg (sq_nonneg θ)
      (sub_nonneg.mpr hθsq)]
  have hsin := Real.sin_ge_sub_cube
    (show 0 ≤ θ/2 by linarith)
  have hsin0 : 0 ≤ Real.sin (θ/2) :=
    Real.sin_nonneg_of_mem_Icc
      ⟨by linarith,by linarith [hθsmall,Real.pi_gt_three]⟩
  have hlow0 : 0 ≤ θ/2-(θ/2)^3/6 := by
    nlinarith [sq_nonneg θ]
  have hsqsin : (θ/2-(θ/2)^3/6)^2 ≤
      Real.sin (θ/2)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsin)
      (add_nonneg hsin0 hlow0)]
  have htrig : 2-2*Real.cos θ=4*Real.sin (θ/2)^2 := by
    have hc : Real.cos θ=2*Real.cos (θ/2)^2-1 := by
      convert Real.cos_two_mul (θ/2) using 1 <;> ring
    have hs := Real.sin_sq_add_cos_sq (θ/2)
    nlinarith
  have hpoly : θ^2-θ^4/12 ≤
      4*(θ/2-(θ/2)^3/6)^2 := by
    nlinarith [sq_nonneg (θ^3)]
  have hnear : (999/1000:ℝ)*θ^2 ≤ θ^2-θ^4/12 := by
    nlinarith [hθfour]
  constructor
  · rw [htrig]
    nlinarith
  · have hc := Real.one_sub_sq_div_two_le_cos (x := θ)
    nlinarith

theorem movingArc_b_le_one_twentieth
    {d : ℝ} (hd0 : 0 < d) (hd : d ≤ 1/1501) :
    Real.sqrt (3*d) ≤ 1/20 := by
  have hsq : Real.sqrt (3*d)^2=3*d :=
    Real.sq_sqrt (by positivity)
  have hroot : 0 ≤ Real.sqrt (3*d) := Real.sqrt_nonneg _
  nlinarith

/-- The moving arc's normalized variance has the sharper `0.995`
constant needed by the third-moment comparison. -/
theorem movingArc_deficit_variance_lower
    {d : ℝ} (hd0 : 0 < d) (hd : d ≤ 1/1501) :
    let b : ℝ := Real.sqrt (3*d)
    let S : ℝ → ℝ := fun θ => 2-2*Real.cos θ
    (1/b)*(∫ θ in (0:ℝ)..b, S θ^2) -
      ((1/b)*(∫ θ in (0:ℝ)..b, S θ))^2 ≥
      (995/1000:ℝ)*4*b^4/45 := by
  dsimp
  let b : ℝ := Real.sqrt (3*d)
  let S : ℝ → ℝ := fun θ => 2-2*Real.cos θ
  have hb : 0 < b := (refinedArc_mean_bounds hd0 hd).1
  have hb0 : 0 ≤ b := hb.le
  have hbshort : b ≤ 1/20 := movingArc_b_le_one_twentieth hd0 hd
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
  have hSupper : (1/b)*(∫ θ in (0:ℝ)..b, S θ) ≤ b^2/3 := by
    have hraw : (∫ θ in (0:ℝ)..b, S θ) ≤
        ∫ θ in (0:ℝ)..b, θ^2 := by
      apply intervalIntegral.integral_mono_on hb0 hIntS hInt2
      intro θ hθ
      exact (movingArc_cos_deficit_quadratic hbshort hθ.1 hθ.2).2
    rw [(coarseArc_polynomial_moments b).1] at hraw
    have hnorm := mul_le_mul_of_nonneg_left hraw
      (show 0 ≤ 1/b by positivity)
    have hpow : (1/b)*(b^3/3)=b^2/3 := by
      field_simp [ne_of_gt hb]
    rw [hpow] at hnorm
    exact hnorm
  have hSsqLower :
      (999/1000:ℝ)^2*b^4/5 ≤
        (1/b)*(∫ θ in (0:ℝ)..b, S θ^2) := by
    have hraw :
        (999/1000:ℝ)^2*(∫ θ in (0:ℝ)..b, θ^4) ≤
          ∫ θ in (0:ℝ)..b, S θ^2 := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on hb0
      · exact hInt4.const_mul _
      · exact hIntSsq
      intro θ hθ
      have hpoint :=
        (movingArc_cos_deficit_quadratic hbshort hθ.1 hθ.2).1
      have hSpos : 0 ≤ S θ := by
        dsimp [S]
        linarith [Real.cos_le_one θ]
      have hθpos : 0 ≤ (999/1000:ℝ)*θ^2 := by positivity
      have hproduct := mul_nonneg (sub_nonneg.mpr hpoint)
        (add_nonneg hSpos hθpos)
      dsimp [S] at *
      nlinarith
    rw [(coarseArc_polynomial_moments b).2] at hraw
    have hnorm := mul_le_mul_of_nonneg_left hraw
      (show 0 ≤ 1/b by positivity)
    have hpow : (1/b)*((999/1000:ℝ)^2*(b^5/5)) =
        (999/1000:ℝ)^2*b^4/5 := by
      field_simp [ne_of_gt hb]
    rw [hpow] at hnorm
    exact hnorm
  have hSmeanSq :
      ((1/b)*(∫ θ in (0:ℝ)..b, S θ))^2 ≤ b^4/9 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hSupper)
      (add_nonneg hS0 (by positivity : 0 ≤ b^2/3))]
  have hb4 : 0 ≤ b^4 := by positivity
  have hnumeric :
      (995/1000:ℝ)*4*b^4/45 ≤
        (999/1000:ℝ)^2*b^4/5-b^4/9 := by
    have hnum := movingArc_variance_rational_margin
    nlinarith
  nlinarith

end SpringerLean

#print axioms SpringerLean.movingArc_cos_deficit_quadratic
#print axioms SpringerLean.movingArc_deficit_variance_lower
