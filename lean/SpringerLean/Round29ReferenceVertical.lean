import SpringerLean.Round29ActualReferenceGlobal
import SpringerLean.Round17CauchyKernel

open MeasureTheory

namespace SpringerLean

/-- The squared complex norm on a vertical line is the Cartesian sum of squares. -/
theorem vertical_complex_norm_sq (a t : ℝ) :
    ‖((a : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 = a ^ 2 + t ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  ring

/-- The complex radial reference restricts to the real vertical reference. -/
theorem radialReferencePotential_vertical (a t : ℝ) :
    radialReferencePotential ((a : ℂ) + (t : ℂ) * Complex.I) =
      verticalReferenceKernel a t := by
  have hsq := vertical_complex_norm_sq a t
  simp only [radialReferencePotential, verticalReferenceKernel, hsq]
  congr 1
  ring

/-- The common reciprocal-quadratic error kernel is integrable on every
vertical line and its integral has the exact Cauchy value. -/
theorem verticalReferenceErrorKernel_integrable (a : ℝ) :
    Integrable (fun t : ℝ => (1 + a ^ 2 + t ^ 2)⁻¹) := by
  let lam : ℝ := Real.sqrt (1 + a ^ 2)
  have hbase : 0 ≤ 1 + a ^ 2 := by positivity
  have hposbase : 0 < 1 + a ^ 2 := by positivity
  have hlam : 0 < lam := Real.sqrt_pos.2 hposbase
  have hlamne : lam ≠ 0 := ne_of_gt hlam
  have hsq : lam ^ 2 = 1 + a ^ 2 := Real.sq_sqrt hbase
  have hfun : (fun t : ℝ => (1 + a ^ 2 + t ^ 2)⁻¹) =
      fun t => lam⁻¹ * (lam / (lam ^ 2 + t ^ 2)) := by
    funext t
    rw [hsq]
    have hden : lam ^ 2 + t ^ 2 ≠ 0 := by positivity
    field_simp [hlamne, hden]
  rw [hfun]
  exact (verticalCauchyKernel_integrable hlam).const_mul lam⁻¹

theorem verticalReferenceErrorKernel_integral (a : ℝ) :
    (∫ t : ℝ, (1 + a ^ 2 + t ^ 2)⁻¹) =
      Real.pi / Real.sqrt (1 + a ^ 2) := by
  let lam : ℝ := Real.sqrt (1 + a ^ 2)
  have hbase : 0 ≤ 1 + a ^ 2 := by positivity
  have hposbase : 0 < 1 + a ^ 2 := by positivity
  have hlam : 0 < lam := Real.sqrt_pos.2 hposbase
  have hlamne : lam ≠ 0 := ne_of_gt hlam
  have hsq : lam ^ 2 = 1 + a ^ 2 := Real.sq_sqrt hbase
  have hfun : (fun t : ℝ => (1 + a ^ 2 + t ^ 2)⁻¹) =
      fun t => lam⁻¹ * (lam / (lam ^ 2 + t ^ 2)) := by
    funext t
    rw [hsq]
    have hden : lam ^ 2 + t ^ 2 ≠ 0 := by positivity
    field_simp [hlamne, hden]
  rw [hfun, integral_const_mul, verticalCauchyKernel_integral hlam]
  simp [lam, div_eq_mul_inv, mul_comm]
end SpringerLean