import SpringerLean.Round1464JFloorAuxiliary
import Mathlib.Analysis.Complex.ExponentialBounds

namespace SpringerLean

/-- A single exponential envelope replaces two logarithmic
monotonicity derivative arguments: for a base log at least six, cubic
growth in an added log is paid by `exp(u/2)`. -/
theorem logCube_exponential_envelope
    {c u : ℝ} (hc : 6 ≤ c) (hu : 0 ≤ u) :
    (c+u)^3 ≤ c^3*Real.exp (u/2) := by
  have hc0 : 0 < c := by linarith
  have hdiv : u/c ≤ u/6 := by
    apply (div_le_div_iff₀ hc0 (by norm_num : (0:ℝ)<6)).2
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hc)]
  have hExp := Real.add_one_le_exp (u/c)
  have hscaled := mul_le_mul_of_nonneg_left hExp hc0.le
  have hfirst : c+u ≤ c*Real.exp (u/c) := by
    have heq : c*(1+u/c)=c+u := by field_simp [ne_of_gt hc0]
    nlinarith [hscaled,heq]
  have hExpMono : Real.exp (u/c) ≤ Real.exp (u/6) :=
    Real.exp_le_exp.mpr hdiv
  have hsecond : c+u ≤ c*Real.exp (u/6) := by
    have hmul := mul_le_mul_of_nonneg_left hExpMono hc0.le
    linarith
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ c+u) hsecond 3
  have heq : (Real.exp (u/6))^3=Real.exp (u/2) := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  calc
    (c+u)^3 ≤ (c*Real.exp (u/6))^3 := hpow
    _ = c^3*Real.exp (u/2) := by rw [mul_pow,heq]

theorem log_3002_gt_six : (6:ℝ) < Real.log 3002 := by
  have hpow := pow_lt_pow_left₀ Real.exp_one_lt_three
    (Real.exp_pos 1).le (by norm_num : (6:ℕ) ≠ 0)
  have hexp : Real.exp 6 < 3002 := by
    have heq : Real.exp 6=(Real.exp 1)^6 := by
      rw [←Real.exp_nat_mul]
      norm_num
    rw [heq]
    nlinarith [hpow]
  exact (Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ)<3002)).2 hexp

end SpringerLean

#print axioms SpringerLean.logCube_exponential_envelope
#print axioms SpringerLean.log_3002_gt_six
