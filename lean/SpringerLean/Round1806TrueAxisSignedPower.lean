import SpringerLean.Round1803TrueAxisLogScalar

namespace SpringerLean
set_option maxHeartbeats 900000

/-- The coarse true-axis logarithmic budget implies the required
lower-power domination, with no optimized sine constants. -/
theorem trueAxis_signed_power_lt_lower
    (N : ℕ) (hN : 750 ≤ N) {u s h gamma theta Lambda : ℝ}
    (hu : 0 < u) (hs : 0 ≤ s) (hsu : s=2*(N : ℝ)*(1-u))
    (hLambda : 0 < Lambda) (hlogLambda : -14 < (2*(N : ℝ))*Real.log Lambda)
    (hcost : (2*(N : ℝ))^2*h^2/2 ≤ 1/6+(5/8 : ℝ)*s)
    (hgammaLo : Real.pi/3 ≤ |gamma|) (hgammaHi : |gamma| ≤ Real.pi/2)
    (hshort : s ≤ 2 → |theta| ≤ 6/7) :
    u^(2*N)*(1+h^2)^N*(1-(8/25 : ℝ)*(Real.sin (gamma-theta))^2) <
      Lambda*u^(2*N-8) := by
  let m := 2*(N : ℝ)
  let f := 1-(8/25 : ℝ)*(Real.sin (gamma-theta))^2
  have hm : (1500 : ℝ) ≤ m := by dsimp [m]; exact_mod_cast (by omega : 1500 ≤ 2*N)
  have hm0 : 0 < m := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hf : 0 < f := by
    have hh := Real.sin_sq_add_cos_sq (gamma-theta)
    have hc := sq_nonneg (Real.cos (gamma-theta))
    dsimp [f]
    nlinarith
  have hH : 0 < 1+h^2 := by positivity
  have hU : 0 < u^(2*N) := pow_pos hu _
  have hP : 0 < (1+h^2)^N := pow_pos hH _
  have hUl : 0 < u^(2*N-8) := pow_pos hu _
  have hlogu := Real.log_le_sub_one_of_pos hu
  have hlogh := Real.log_le_sub_one_of_pos hH
  have hlogf := Real.log_le_sub_one_of_pos hf
  have hmu := mul_le_mul_of_nonneg_left hlogu hm0.le
  have hmh := mul_le_mul_of_nonneg_left hlogh (mul_nonneg hm0.le hN0)
  have hmf := mul_le_mul_of_nonneg_left hlogf hm0.le
  have hnegative := trueAxis_scalar_log_cost_negative hm hs hcost hgammaLo hgammaHi hshort
  change u^(2*N)*(1+h^2)^N*f < Lambda*u^(2*N-8)
  apply (Real.log_lt_log_iff (mul_pos (mul_pos hU hP) hf) (mul_pos hLambda hUl)).mp
  rw [Real.log_mul (mul_pos hU hP).ne' hf.ne', Real.log_mul hU.ne' hP.ne',
    Real.log_mul hLambda.ne' hUl.ne', Real.log_pow, Real.log_pow, Real.log_pow]
  rw [Nat.cast_sub (by omega : 8 ≤ 2*N)]
  push_cast
  apply (mul_lt_mul_iff_left₀ hm0).mp
  dsimp [m, f] at *
  nlinarith [hmu,hmh,hmf,hnegative,hlogLambda,hsu]

end SpringerLean

#print axioms SpringerLean.trueAxis_signed_power_lt_lower
