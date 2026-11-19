import SpringerLean.Round1772CentralExponentialBudget

namespace SpringerLean
set_option maxHeartbeats 500000

/-- A coarse logarithm bound replaces logarithmic differentiation of
the central allowance. The only numerical input is 10000<2^14. -/
theorem large_log_hundred_mul_le {m : ℕ} (hm : 1500 ≤ m) :
    Real.log (100*(m : ℝ)) ≤ (m : ℝ)/20 := by
  have hm' : (1500 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have h2 : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hbig : Real.log (10000 : ℝ) ≤ 14 := by
    have hh : Real.log (10000 : ℝ) ≤ Real.log ((2 : ℝ)^14) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have hsmall := Real.log_le_sub_one_of_pos (div_pos hm0 (by norm_num : (0 : ℝ) < 100))
  have hprod : 100*(m : ℝ)=10000*((m : ℝ)/100) := by ring
  rw [hprod, Real.log_mul (by norm_num : (10000 : ℝ) ≠ 0)
    (by positivity : (m : ℝ)/100 ≠ 0)]
  nlinarith

/-- Outside the joint tiny-deficit regime the standard logarithmic
cutoff implies the simpler cutoff of central_cost_lt_cubic. -/
theorem central_cost_lt_cubic_of_log_cutoff
    {m : ℕ} (hm : 1500 ≤ m) {D : ℝ}
    (hD : (3/100 : ℝ)/((m : ℝ)*Real.log (100*(m : ℝ))) ≤ D) :
    (m : ℝ)*Real.sqrt (m : ℝ)*(23/25 : ℝ)^m < D^3/1000 := by
  have hm' : (1500 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hL0 : 0 < Real.log (100*(m : ℝ)) := Real.log_pos (by nlinarith)
  have hL := large_log_hundred_mul_le hm
  have hcoarse : 1/(2*(m : ℝ)^2) ≤
      (3/100 : ℝ)/((m : ℝ)*Real.log (100*(m : ℝ))) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2*(m : ℝ)^2)
      (mul_pos hm0 hL0)).mpr
    have hh := mul_le_mul_of_nonneg_left hL hm0.le
    nlinarith
  exact central_cost_lt_cubic hm (hcoarse.trans hD)

end SpringerLean

#print axioms SpringerLean.central_cost_lt_cubic_of_log_cutoff
