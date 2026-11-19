import SpringerLean.Round1436MovingArcThirdControl
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace SpringerLean
set_option maxHeartbeats 150000

/-- The affine power retains a deficit-dependent exponential factor
through the entire moving arc. The condition `n*s≤4` is the only
input to this logarithmic comparison. -/
theorem movingArc_power_exponential_lower
    (n : ℕ) (hn : 3 ≤ n) {s : ℝ}
    (hs0 : 0 ≤ s) (hns : (n:ℝ)*s ≤ 4) :
    Real.exp (-(n:ℝ)*s/2) ≤ (1-s/2)^(n-2) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hsm : s/2 < 1 := by
    have hnLarge : (3:ℝ)≤n := by exact_mod_cast hn
    by_contra h
    have h2 : 2 ≤ s := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith :
      0 ≤ (n:ℝ)-3)) (sub_nonneg.mpr h2)]
  have hOne : 0 < 1-s/2 := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hOne
  have hm : 0 ≤ ((n-2:ℕ):ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hlog hm
  have hNat : ((n-2:ℕ):ℝ)=(n:ℝ)-2 := by
    rw [Nat.cast_sub (by omega : 2≤n)]
    norm_num
  have haux : -(n:ℝ)*s/2 ≤
      ((n-2:ℕ):ℝ)*(1-(1-s/2)⁻¹) := by
    rw [hNat]
    have hOneNe : 1-s/2 ≠ 0 := ne_of_gt hOne
    have hfrac : 1-(1-s/2)⁻¹ = -(s/2)/(1-s/2) := by
      field_simp [hOneNe, show 2-s ≠ 0 by linarith]
      ring
    rw [hfrac]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hOne).2
    have hh := mul_le_mul_of_nonneg_right hns hs0
    nlinarith
  have hlogBound : -(n:ℝ)*s/2 ≤
      ((n-2:ℕ):ℝ)*Real.log (1-s/2) :=
    haux.trans hmul
  have hExp := Real.exp_le_exp.mpr hlogBound
  have hpow : Real.exp (((n-2:ℕ):ℝ)*Real.log (1-s/2)) =
      (1-s/2)^(n-2) := by
    rw [Real.exp_nat_mul,Real.exp_log hOne]
  exact hExp.trans_eq hpow

end SpringerLean

#print axioms SpringerLean.movingArc_power_exponential_lower
