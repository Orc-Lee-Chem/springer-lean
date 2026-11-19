import SpringerLean.Round1433MovingArcMoments

open MeasureTheory

namespace SpringerLean
set_option maxHeartbeats 200000

/-- Raw cubic difference upper bound using only the first and sixth
ordinary polynomial arc moments. -/
theorem movingArc_deficit_third_moment_upper
    {d : ℝ} (hd0 : 0 < d) (hd : d ≤ 1/1501) :
    let b : ℝ := Real.sqrt (3*d)
    let S : ℝ → ℝ := fun θ => 2-2*Real.cos θ
    (1/b)*(∫ θ in (0:ℝ)..b, S θ^3) -
      ((1/b)*(∫ θ in (0:ℝ)..b, S θ))^3 ≤
      b^6*((1/7:ℝ)-(999/1000:ℝ)^3/27) := by
  dsimp
  let b : ℝ := Real.sqrt (3*d)
  let S : ℝ → ℝ := fun θ => 2-2*Real.cos θ
  have hb : 0 < b := (refinedArc_mean_bounds hd0 hd).1
  have hb0 : 0 ≤ b := hb.le
  have hbshort : b ≤ 1/20 := movingArc_b_le_one_twentieth hd0 hd
  have hIntS : IntervalIntegrable S volume 0 b := by
    apply Continuous.intervalIntegrable
    dsimp [S]; fun_prop
  have hIntCube : IntervalIntegrable
      (fun θ : ℝ => S θ^3) volume 0 b := by
    apply Continuous.intervalIntegrable
    dsimp [S]; fun_prop
  have hInt2 : IntervalIntegrable
      (fun θ : ℝ => θ^2) volume 0 b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hInt6 : IntervalIntegrable
      (fun θ : ℝ => θ^6) volume 0 b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hmeanLower :
      (999/1000:ℝ)*b^2/3 ≤
        (1/b)*(∫ θ in (0:ℝ)..b, S θ) := by
    have hraw :
        (999/1000:ℝ)*(∫ θ in (0:ℝ)..b, θ^2) ≤
          ∫ θ in (0:ℝ)..b, S θ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on hb0
      · exact hInt2.const_mul _
      · exact hIntS
      intro θ hθ
      exact (movingArc_cos_deficit_quadratic
        hbshort hθ.1 hθ.2).1
    rw [(coarseArc_polynomial_moments b).1] at hraw
    have hh := mul_le_mul_of_nonneg_left hraw
      (show 0 ≤ 1/b by positivity)
    have hpow : (1/b)*((999/1000:ℝ)*(b^3/3)) =
        (999/1000:ℝ)*b^2/3 := by
      field_simp [ne_of_gt hb]
    rw [hpow] at hh
    exact hh
  have hcubeUpper :
      (1/b)*(∫ θ in (0:ℝ)..b, S θ^3) ≤ b^6/7 := by
    have hraw : (∫ θ in (0:ℝ)..b, S θ^3) ≤
        ∫ θ in (0:ℝ)..b, θ^6 := by
      apply intervalIntegral.integral_mono_on hb0 hIntCube hInt6
      intro θ hθ
      have hpoint := (movingArc_cos_deficit_quadratic
        hbshort hθ.1 hθ.2).2
      have hS0 : 0 ≤ S θ := by
        dsimp [S]
        linarith [Real.cos_le_one θ]
      have hpow : S θ^3 ≤ (θ^2)^3 :=
        pow_le_pow_left₀ hS0 hpoint 3
      nlinarith [hpow]
    rw [integral_pow] at hraw
    norm_num at hraw
    have hh := mul_le_mul_of_nonneg_left hraw
      (show 0 ≤ 1/b by positivity)
    have hpow : (1/b)*(b^7/7)=b^6/7 := by
      field_simp [ne_of_gt hb]
    rw [hpow] at hh
    exact hh
  have hmeanCube :
      ((999/1000:ℝ)*b^2/3)^3 ≤
        ((1/b)*(∫ θ in (0:ℝ)..b, S θ))^3 :=
    pow_le_pow_left₀ (by positivity) hmeanLower 3
  nlinarith [hmeanCube,hcubeUpper]

end SpringerLean

#print axioms SpringerLean.movingArc_deficit_third_moment_upper
