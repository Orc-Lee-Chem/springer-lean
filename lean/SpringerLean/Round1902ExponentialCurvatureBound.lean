import SpringerLean.Round1901ExponentialQuadraticLower
import Mathlib.Analysis.Complex.ExponentialBounds

namespace SpringerLean

theorem exp_two_gt_twenty_two_thirds :
    (22 / 3 : ℝ) < Real.exp 2 := by
  have h := Real.exp_one_gt_d9
  have hb : (2718 / 1000 : ℝ) < Real.exp 1 := by
    exact lt_trans (by norm_num) h
  have hsq := pow_lt_pow_left₀ hb (by norm_num : (0 : ℝ) ≤ 2718 / 1000)
    (by decide : (2 : ℕ) ≠ 0)
  rw [← Real.exp_nat_mul] at hsq
  norm_num at hsq
  exact lt_trans (by norm_num) hsq

private theorem exp_three_gt_twenty :
    (20 : ℝ) < Real.exp 3 := by
  have h := Real.exp_one_gt_d9
  have hb : (2718 / 1000 : ℝ) < Real.exp 1 := by
    exact lt_trans (by norm_num) h
  have hc := pow_lt_pow_left₀ hb (by norm_num : (0 : ℝ) ≤ 2718 / 1000)
    (by decide : (3 : ℕ) ≠ 0)
  rw [← Real.exp_nat_mul] at hc
  norm_num at hc
  exact lt_trans (by norm_num) hc

/-- A rational, paper-checkable substitute for maximizing
(v²-2v)exp(-v). For v≥3 the quadratic lower bound at v-3 yields
exp(v) > 20(1+u+u²/2), whose difference from 6v(v-2) is
4(u-1/2)²+1. The remaining interval uses exp(2)>22/3. -/
theorem six_mul_curvature_quadratic_le_exp
    {v : ℝ} (hv : 0 ≤ v) :
    6 * (v ^ 2 - 2 * v) ≤ Real.exp v := by
  by_cases hv2 : v ≤ 2
  · have hp := Real.exp_pos v
    nlinarith [mul_nonneg hv (sub_nonneg.mpr hv2)]
  · by_cases hv3 : v ≤ 3
    · let u := v - 2
      have hu0 : 0 ≤ u := by dsimp [u]; linarith
      have hu1 : u ≤ 1 := by dsimp [u]; linarith
      have hquad := exp_ge_one_add_self_add_half_sq hu0
      have hbase : 0 ≤ 1 + u + u ^ 2 / 2 := by positivity
      have hproduct :
          (22 / 3 : ℝ) * (1 + u + u ^ 2 / 2) ≤ Real.exp v := by
        have heq : v = 2 + u := by dsimp [u]; ring
        rw [heq, Real.exp_add]
        calc
          _ ≤ Real.exp 2 * (1 + u + u ^ 2 / 2) := by
            simpa only [mul_comm] using
              mul_le_mul_of_nonneg_right exp_two_gt_twenty_two_thirds.le hbase
          _ ≤ Real.exp 2 * Real.exp u :=
            mul_le_mul_of_nonneg_left hquad (Real.exp_pos 2).le
      have hnonneg : 0 ≤ (1 - u) * (1 + u) :=
        mul_nonneg (by linarith) (by linarith)
      dsimp [u] at *
      nlinarith
    · let u := v - 3
      have hu0 : 0 ≤ u := by dsimp [u]; linarith
      have hquad := exp_ge_one_add_self_add_half_sq hu0
      have hbase : 0 ≤ 1 + u + u ^ 2 / 2 := by positivity
      have hproduct :
          (20 : ℝ) * (1 + u + u ^ 2 / 2) ≤ Real.exp v := by
        have heq : v = 3 + u := by dsimp [u]; ring
        rw [heq, Real.exp_add]
        calc
          _ ≤ Real.exp 3 * (1 + u + u ^ 2 / 2) := by
            simpa only [mul_comm] using
              mul_le_mul_of_nonneg_right exp_three_gt_twenty.le hbase
          _ ≤ Real.exp 3 * Real.exp u :=
            mul_le_mul_of_nonneg_left hquad (Real.exp_pos 3).le
      dsimp [u] at *
      nlinarith [sq_nonneg (v - 3 - 1 / 2)]

theorem curvature_exp_negative_le_one_sixth
    {v : ℝ} (hv : 0 ≤ v) :
    (v ^ 2 - 2 * v) * Real.exp (-v) ≤ 1 / 6 := by
  have h := six_mul_curvature_quadratic_le_exp hv
  have hm := mul_le_mul_of_nonneg_right h (Real.exp_nonneg (-v))
  rw [← Real.exp_add] at hm
  have heq : v + -v = 0 := by ring
  rw [heq, Real.exp_zero] at hm
  nlinarith

end SpringerLean

#print axioms SpringerLean.curvature_exp_negative_le_one_sixth
