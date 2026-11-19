import SpringerLean.Round1476ActualDeficitUnderThreeTwentieths

namespace SpringerLean
set_option maxHeartbeats 180000

/-- A rational exponential lower bound gives the base logarithmic
constant needed for the stronger cubic estimate. -/
theorem refinedAffine_small_base_log_lt_991 :
    Real.log (2*(1501:ℝ)/(3/20:ℝ)) < 991/100 := by
  have hbase : (1359/500:ℝ)<Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have hpow := pow_lt_pow_left₀ hbase
    (by norm_num : (0:ℝ) ≤ 1359/500)
    (by norm_num : (10:ℕ) ≠ 0)
  have hten : (1359/500:ℝ)^10 < Real.exp 10 := by
    have heq : Real.exp 10=(Real.exp 1)^10 := by
      rw [←Real.exp_nat_mul]
      norm_num
    rw [heq]
    exact hpow
  have hneg : (91/100:ℝ) ≤ Real.exp (-(9/100:ℝ)) := by
    linarith [Real.add_one_le_exp (-(9/100:ℝ))]
  have hpos : 0 < Real.exp (-(9/100:ℝ)) := Real.exp_pos _
  have hmul1 := mul_lt_mul_of_pos_right hten hpos
  have hmul2 := mul_le_mul_of_nonneg_left hneg
    (by positivity : (0:ℝ) ≤ (1359/500)^10)
  have hnum : 2*(1501:ℝ)/(3/20:ℝ) <
      (1359/500:ℝ)^10*(91/100:ℝ) := by norm_num
  have hexp : 2*(1501:ℝ)/(3/20:ℝ)<Real.exp (991/100:ℝ) := by
    have heq : Real.exp (991/100:ℝ)=
        Real.exp 10*Real.exp (-(9/100:ℝ)) := by
      rw [←Real.exp_add]
      congr 1
      norm_num
    rw [heq]
    nlinarith [hmul1,hmul2,hnum]
  exact (Real.log_lt_iff_lt_exp
    (by norm_num : (0:ℝ)<2*1501/(3/20))).2 hexp

theorem refinedAffine_small_base_sqrt_lt_39 :
    Real.sqrt (3/20:ℝ) < 39/100 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3/20),
    Real.sqrt_nonneg (3/20:ℝ)]

theorem refinedAffine_small_base_core_100 :
    100*(17/50:ℝ)^3*Real.sqrt (3/20:ℝ)*
      (Real.log (2*(1501:ℝ)/(3/20:ℝ)))^3 < 1501 := by
  have hs := refinedAffine_small_base_sqrt_lt_39
  have hl := refinedAffine_small_base_log_lt_991
  have hl0 : 0 ≤ Real.log (2*(1501:ℝ)/(3/20:ℝ)) := by
    apply Real.log_nonneg
    norm_num
  have hp := pow_lt_pow_left₀ hl hl0
    (by norm_num : (3:ℕ) ≠ 0)
  have hnum : 100*(17/50:ℝ)^3*(39/100:ℝ)*
      (991/100:ℝ)^3 < 1501 := by norm_num
  have hmul1 := mul_lt_mul_of_pos_right hs
    (by positivity : 0 < 100*(17/50:ℝ)^3*
      (Real.log (2*(1501:ℝ)/(3/20:ℝ)))^3)
  have hmul2 := mul_lt_mul_of_pos_left hp
    (by norm_num : 0 < 100*(17/50:ℝ)^3*(39/100:ℝ))
  nlinarith [hmul1,hmul2,hnum]

end SpringerLean

#print axioms SpringerLean.refinedAffine_small_base_core_100
