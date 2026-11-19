import SpringerLean.Round1463ActualJointJ

namespace SpringerLean

/-- The cubic floor has a manifestly nonnegative factorization for
every nonnegative width parameter. -/
theorem refinedAffine_J_cubic_floor {z : ℝ} (hz : 0 ≤ z) :
    -(9/160:ℝ) ≤
      (5/2:ℝ)*z^3-(11/40:ℝ)*z^2-(57/200:ℝ)*z := by
  have hfactor :
      (5/2:ℝ)*z^3-(11/40:ℝ)*z^2-(57/200:ℝ)*z+9/160 =
      (z-1/4)^2*((5/2:ℝ)*z+9/10)+
        (3/40:ℝ)*z^2+(7/800:ℝ)*z := by ring
  have hnonneg : 0 ≤
      (z-1/4)^2*((5/2:ℝ)*z+9/10)+
        (3/40:ℝ)*z^2+(7/800:ℝ)*z := by positivity
  linarith

/-- A twelve-step Bernoulli bound gives the needed exponential
reserve without a Taylor remainder theorem. -/
theorem refinedAffine_exp_neg_061_gt :
    (8/15:ℝ) < Real.exp (-(61/100:ℝ)) := by
  have hbase := Real.add_one_le_exp (-(61/1200:ℝ))
  have hbase' : (1139/1200:ℝ) ≤
      Real.exp (-(61/1200:ℝ)) := by nlinarith [hbase]
  have hpow := pow_le_pow_left₀
    (by norm_num : (0:ℝ) ≤ 1139/1200) hbase' 12
  have hrat : (8/15:ℝ) < (1139/1200:ℝ)^12 := by norm_num
  have heq : Real.exp (-(61/100:ℝ)) =
      (Real.exp (-(61/1200:ℝ)))^12 := by
    rw [←Real.exp_nat_mul]
    congr 1
    norm_num
  rw [heq]
  exact hrat.trans_le hpow

theorem refinedAffine_exp_neg_061t_gt
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1) :
    (8/15:ℝ) < Real.exp (-(61/100:ℝ)*t) := by
  have hmono : Real.exp (-(61/100:ℝ)) ≤
      Real.exp (-(61/100:ℝ)*t) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact refinedAffine_exp_neg_061_gt.trans_le hmono

end SpringerLean

#print axioms SpringerLean.refinedAffine_J_cubic_floor
#print axioms SpringerLean.refinedAffine_exp_neg_061t_gt
