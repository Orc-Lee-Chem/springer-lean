import SpringerLean.Round1956OddStarBoundaryPushforward
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

open MeasureTheory

namespace SpringerLean

/-- Multiplying the angle by a positive integer preserves the average
of a continuous periodic real-valued test over one full period. -/
theorem periodic_integral_comp_nat_mul
    (f : ℝ → ℝ) (T : ℝ) (hf : Function.Periodic f T)
    (hcont : Continuous f) (m : ℕ) (hm : 0 < m) :
    (∫ θ in 0..T, f ((m : ℝ) * θ)) = ∫ θ in 0..T, f θ := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hInt : ∀ a b : ℝ, IntervalIntegrable f volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have hperiod := hf.intervalIntegral_add_zsmul_eq (m : ℤ) 0 hInt
  have hperiod' :
      (∫ x in 0..(m : ℝ) * T, f x) =
        (m : ℝ) * ∫ x in 0..T, f x := by
    simpa [zsmul_eq_mul, nsmul_eq_mul, mul_comm] using hperiod
  rw [intervalIntegral.integral_comp_mul_left f hm0]
  simp only [mul_zero, zero_mul, hperiod', smul_eq_mul]
  field_simp [hm0]

end SpringerLean

#print axioms SpringerLean.periodic_integral_comp_nat_mul
