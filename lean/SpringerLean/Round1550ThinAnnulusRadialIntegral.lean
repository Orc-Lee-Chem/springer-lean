import SpringerLean.Round1549ActualThinAnnulusCircleGain

open MeasureTheory

namespace SpringerLean
set_option maxHeartbeats 320000

/-- Exact radial integration of the factor supplied by the circle loss.
The polar Jacobian contributes `2r` exactly once. -/
theorem thinAnnulus_radial_power_integral
    {m : ℕ} (hm : 2 ≤ m) (a b : ℝ) :
    (∫ r in a..b, 2*r*(2*r)^(m-2)) =
      2^(m-1:ℕ)*((b^m-a^m)/(m:ℝ)) := by
  have hm1 : m-2+1=m-1 := by omega
  have hm2 : m-1+1=m := by omega
  have hpoint (r : ℝ) : 2*r*(2*r)^(m-2) =
      2^(m-1:ℕ)*r^(m-1) := by
    rw [mul_pow,←hm1,pow_succ,pow_succ]
    ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul,integral_pow]
  rw [hm2]
  have hmCast : ((m-1:ℕ):ℝ)+1=(m:ℝ) := by
    exact_mod_cast hm2
  rw [hmCast]

end SpringerLean

#print axioms SpringerLean.thinAnnulus_radial_power_integral
