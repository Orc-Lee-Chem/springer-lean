import SpringerLean.Round1536CotangentTailIntegral

namespace SpringerLean
set_option maxHeartbeats 320000

/-- The upper endpoint term in the Poisson tail integral is controlled
without any small-angle asymptotic argument. -/
theorem halfAngle_cotangent_le_two_div
    {h : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi) :
    Real.cos (h/2)/Real.sin (h/2) ≤ 2/h := by
  let x := h/2
  have hx0 : 0 < x := by dsimp [x]; linarith
  have hxpi : x < Real.pi := by dsimp [x]; linarith [Real.pi_pos]
  have hxabs : |x| ≤ Real.pi := by rw [abs_of_pos hx0]; exact hxpi.le
  have hs0 : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 hxpi
  have hs : x-x^3/6 ≤ Real.sin x := Real.sin_ge_sub_cube hx0.le
  have hc := Real.cos_le_one_sub_mul_cos_sq hxabs
  have hpiupper : Real.pi < (17/5:ℝ) := by
    have hp := Real.pi_lt_d20
    norm_num at hp ⊢
    linarith
  have hpi2 : Real.pi^2 < 12 := by nlinarith [Real.pi_pos]
  have hcoef : (1/6:ℝ) ≤ 2/Real.pi^2 := by
    have hp2 : 0 < Real.pi^2 := sq_pos_of_pos Real.pi_pos
    apply (le_div_iff₀ hp2).2
    nlinarith [hpi2.le]
  have hx3 : 0 ≤ x^3 := by positivity
  have hcoef' := mul_le_mul_of_nonneg_right hcoef hx3
  have hc' := mul_le_mul_of_nonneg_left hc hx0.le
  have hmain : x*Real.cos x ≤ Real.sin x := by
    nlinarith [hs,hcoef',hc']
  have hden : 0 < h*Real.sin x := mul_pos hh0 hs0
  apply (div_le_div_iff₀ hs0 hh0).2
  dsimp [x] at hmain ⊢
  nlinarith [hmain]

end SpringerLean

#print axioms SpringerLean.halfAngle_cotangent_le_two_div
