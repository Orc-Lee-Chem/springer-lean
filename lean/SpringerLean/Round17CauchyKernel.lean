import SpringerLean.Round16VerticalPrelude
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory

namespace SpringerLean

/-- The nonnegative parameter kernel for the vertical-line logarithm is
integrable for every positive parameter. -/
theorem verticalCauchyKernel_integrable {lam : ℝ} (hlam : 0 < lam) :
    Integrable (fun t : ℝ => lam / (lam ^ 2 + t ^ 2)) := by
  have h0 : lam ≠ 0 := ne_of_gt hlam
  have hbase : Integrable (fun t : ℝ => (1 + (lam⁻¹ * t) ^ 2)⁻¹) :=
    integrable_inv_one_add_mul_sq (inv_ne_zero h0)
  convert hbase.const_mul lam⁻¹ using 1
  funext t
  field_simp [h0]

/-- The integral of the positive Cauchy kernel is exactly pi, independent
of its positive scale parameter. -/
theorem verticalCauchyKernel_integral {lam : ℝ} (hlam : 0 < lam) :
    ∫ t : ℝ, lam / (lam ^ 2 + t ^ 2) = Real.pi := by
  have h0 : lam ≠ 0 := ne_of_gt hlam
  have hfun : (fun t : ℝ => lam / (lam ^ 2 + t ^ 2)) =
      (fun t : ℝ => lam⁻¹ * (1 + (lam⁻¹ * t) ^ 2)⁻¹) := by
    funext t
    field_simp [h0]
  rw [hfun, MeasureTheory.integral_const_mul, integral_univ_inv_one_add_mul_sq]
  rw [abs_inv, abs_of_pos hlam]
  field_simp [h0]

end SpringerLean
