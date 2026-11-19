import SpringerLean.Round1775ComparisonPositiveCatalan
import SpringerLean.Round661CatalanRadiusScalar

namespace SpringerLean
set_option maxHeartbeats 700000

/-- Positive even disk moments satisfy the semicircle recurrence.
The zeroth-power convention is deliberately excluded. -/
theorem comparisonPositiveDiskMoment_even_step
    (q : ℕ) (hq : 1 ≤ q) :
    (2*(q : ℝ)+4)*comparisonPositiveDiskMoment (2*q+2)=
      (2*(q : ℝ)+1)*comparisonPositiveDiskMoment (2*q) := by
  have hcur : (2 : ℝ)^(2*q+1)*comparisonPositiveDiskMoment (2*q)=(catalan q : ℝ) := by
    have hh := comparisonPositiveDiskMoment_catalan (k := q+1) (by omega : 2 ≤ q+1)
    simpa only [show 2*(q+1)-2=2*q by omega, Nat.add_sub_cancel] using hh
  have hnext : (2 : ℝ)^(2*q+2+1)*comparisonPositiveDiskMoment (2*q+2)=(catalan (q+1) : ℝ) := by
    have hh := comparisonPositiveDiskMoment_catalan (k := q+2) (by omega : 2 ≤ q+2)
    simpa only [show 2*(q+2)-2=2*q+2 by omega, show q+2-1=q+1 by omega] using hh
  have hc := catalan_real_step q
  rw [←hcur,←hnext] at hc
  have hp : (2 : ℝ)^(2*q+2+1)=4*(2 : ℝ)^(2*q+1) := by
    calc
      _ = (2 : ℝ)^(2*q+1)*(2 : ℝ)^2 := by rw [←pow_add]
      _ = _ := by ring
  rw [hp] at hc
  apply mul_left_cancel₀ (by positivity : (2*(2 : ℝ)^(2*q+1)) ≠ 0)
  nlinarith

theorem comparisonPositiveDiskMoment_even_step_solved
    (q : ℕ) (hq : 1 ≤ q) :
    comparisonPositiveDiskMoment (2*q+2)=
      ((2*(q : ℝ)+1)/(2*(q : ℝ)+4))*comparisonPositiveDiskMoment (2*q) := by
  have hh := comparisonPositiveDiskMoment_even_step q hq
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (by positivity : 2*(q : ℝ)+4 ≠ 0)).mpr
  nlinarith

end SpringerLean

#print axioms SpringerLean.comparisonPositiveDiskMoment_even_step
