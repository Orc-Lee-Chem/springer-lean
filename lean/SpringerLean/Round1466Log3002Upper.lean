import SpringerLean.Round1465LogCubeEnvelope

namespace SpringerLean

theorem log_3002_lt_81_10 : Real.log 3002 < (81/10:ℝ) := by
  have hE1 : (27/10:ℝ) < Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have hE01 : (11/10:ℝ) ≤ Real.exp (1/10:ℝ) := by
    linarith [Real.add_one_le_exp (1/10:ℝ)]
  have hpow := pow_lt_pow_left₀ hE1
    (by norm_num : (0:ℝ) ≤ 27/10)
    (by norm_num : (8:ℕ) ≠ 0)
  have hmul := mul_lt_mul_of_pos_right hpow
    (Real.exp_pos (1/10:ℝ))
  have hmul2 := mul_le_mul_of_nonneg_left hE01
    (by positivity : (0:ℝ) ≤ (27/10)^8)
  have hnum : (3002:ℝ) < (27/10:ℝ)^8*(11/10:ℝ) := by norm_num
  have hexp : (3002:ℝ) < Real.exp (81/10:ℝ) := by
    have heq : Real.exp (81/10:ℝ) =
        (Real.exp 1)^8*Real.exp (1/10:ℝ) := by
      have hsum : (81/10:ℝ)=8*1+1/10 := by norm_num
      rw [hsum,Real.exp_add]
      congr 1
      rw [←Real.exp_nat_mul]
      norm_num
    rw [heq]
    nlinarith [hmul,hmul2,hnum]
  exact (Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ)<3002)).2 hexp

end SpringerLean

#print axioms SpringerLean.log_3002_lt_81_10
