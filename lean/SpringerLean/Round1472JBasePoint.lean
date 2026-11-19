import SpringerLean.Round1471ActualIndividualJ
import Mathlib.Analysis.Complex.ExponentialBounds

namespace SpringerLean
set_option maxHeartbeats 150000

theorem refinedAffine_base_sqrt_gt :
    (12/31:ℝ) < Real.sqrt (3/20:ℝ) := by
  have hs : (Real.sqrt (3/20:ℝ))^2=3/20 :=
    Real.sq_sqrt (by norm_num)
  have hnonneg := Real.sqrt_nonneg (3/20:ℝ)
  nlinarith

theorem refinedAffine_base_exp_lower :
    (1-(183/4000:ℝ))^2 ≤
      Real.exp (-(183/2000:ℝ)) := by
  have hbase := Real.add_one_le_exp (-(183/4000:ℝ))
  have hbase' : (1-(183/4000:ℝ)) ≤
      Real.exp (-(183/4000:ℝ)) := by nlinarith [hbase]
  have hpow := pow_le_pow_left₀
    (by norm_num : (0:ℝ) ≤ 1-183/4000) hbase' 2
  have heq : Real.exp (-(183/2000:ℝ)) =
      (Real.exp (-(183/4000:ℝ)))^2 := by
    rw [←Real.exp_nat_mul]
    congr 1
    norm_num
  rw [heq]
  exact hpow

/-- A rational two-step exponential lower bound already clears the
needed 0.58 margin at the critical base point. -/
theorem refinedAffine_J_base_gt_058 :
    (58/100:ℝ) <
      (67/1000:ℝ)*1501*(3/20:ℝ)^2*
        Real.sqrt (3/20:ℝ)*Real.exp (-(61/100:ℝ)*(3/20:ℝ))-
      (285/1000:ℝ)*0.51-(275/1000:ℝ)*(0.51:ℝ)^2 := by
  have hroot := refinedAffine_base_sqrt_gt
  have hexp := refinedAffine_base_exp_lower
  have heq : -(61/100:ℝ)*(3/20:ℝ)=-(183/2000:ℝ) := by norm_num
  rw [heq]
  have hpositive : 0 < Real.exp (-(183/2000:ℝ)) := Real.exp_pos _
  have hprod1 := mul_lt_mul_of_pos_right hroot hpositive
  have hprod2 := mul_le_mul_of_nonneg_left hexp
    (by norm_num : (0:ℝ) ≤ 12/31)
  have hnum : (58/100:ℝ) <
      (67/1000:ℝ)*1501*(3/20:ℝ)^2*(12/31:ℝ)*
        (1-(183/4000:ℝ))^2-
      (285/1000:ℝ)*(51/100:ℝ)-
      (275/1000:ℝ)*(51/100:ℝ)^2 := by norm_num
  nlinarith [hprod1,hprod2,hnum]

theorem refinedAffine_base_z_lt_051 :
    (17/50:ℝ)*(3/20)*
      Real.log (2*(1501:ℝ)/(3/20:ℝ)) < 51/100 := by
  have hE1 : (27/10:ℝ)<Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have hpow := pow_lt_pow_left₀ hE1
    (by norm_num : (0:ℝ) ≤ 27/10)
    (by norm_num : (10:ℕ) ≠ 0)
  have hexp : 2*(1501:ℝ)/(3/20:ℝ) < Real.exp 10 := by
    have heq : Real.exp 10=(Real.exp 1)^10 := by
      rw [←Real.exp_nat_mul]
      norm_num
    rw [heq]
    nlinarith [hpow]
  have hlog : Real.log (2*(1501:ℝ)/(3/20:ℝ)) < 10 :=
    (Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ)<2*1501/(3/20))).2 hexp
  nlinarith

theorem refinedAffine_J_base_actual_gt_058 :
    (58/100:ℝ) < refinedAffineJ 1501 (3/20) := by
  let z : ℝ := (17/50)*(3/20)*
    Real.log (2*(1501:ℝ)/(3/20:ℝ))
  have hz : z < 51/100 := refinedAffine_base_z_lt_051
  have hz0 : 0 ≤ z := by
    have harg : (1:ℝ)<2*(1501:ℝ)/(3/20:ℝ) := by norm_num
    dsimp [z]
    have hlog := Real.log_pos harg
    positivity
  have hsq : z^2 ≤ (51/100:ℝ)^2 :=
    pow_le_pow_left₀ hz0 hz.le 2
  have hbase := refinedAffine_J_base_gt_058
  unfold refinedAffineJ
  change (58/100:ℝ) <
    (67/1000:ℝ)*1501*(3/20:ℝ)^2*
      Real.sqrt (3/20:ℝ)*Real.exp (-(61/100:ℝ)*(3/20:ℝ))-
    (285/1000:ℝ)*z-(275/1000:ℝ)*z^2
  nlinarith [hbase,hz,hsq]

end SpringerLean

#print axioms SpringerLean.refinedAffine_J_base_gt_058
#print axioms SpringerLean.refinedAffine_base_z_lt_051
#print axioms SpringerLean.refinedAffine_J_base_actual_gt_058
