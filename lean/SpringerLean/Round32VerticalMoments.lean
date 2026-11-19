import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import SpringerLean.Round31AuxLocalSubmean

open MeasureTheory Set Metric

namespace SpringerLean

/-- The mean imaginary coordinate on a circle is its center's imaginary coordinate. -/
theorem circleAverage_im (c : ℂ) (ρ : ℝ) :
    Real.circleAverage (fun z : ℂ => z.im) c ρ = c.im := by
  rw [Real.circleAverage_def]
  change (2 * Real.pi)⁻¹ *
    (∫ θ in (0:ℝ)..2 * Real.pi, (circleMap c ρ θ).im) = c.im
  have hmap (θ : ℝ) : (circleMap c ρ θ).im =
      c.im + ρ * Real.sin θ := by
    rw [show circleMap c ρ θ = c + circleMap 0 ρ θ from by simp [circleMap]]
    simp [Complex.add_im, circleMap_zero_im]
  simp_rw [hmap]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_sin]
  · have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hcos : Real.cos (Real.pi * 2) = 1 := by
      convert Real.cos_two_pi using 1 <;> ring
    have hsin : Real.sin (Real.pi * 2) = 0 := by
      convert Real.sin_two_pi using 1 <;> ring
    field_simp <;> simp [Real.cos_two_pi, Real.sin_two_pi] <;> ring
  · exact (by fun_prop : Continuous _).intervalIntegrable _ _
  · exact (by fun_prop : Continuous _).intervalIntegrable _ _

/-- The mean squared imaginary coordinate has the variance ρ²/2. -/
theorem circleAverage_im_sq (c : ℂ) (ρ : ℝ) :
    Real.circleAverage (fun z : ℂ => z.im ^ 2) c ρ =
      c.im ^ 2 + ρ ^ 2 / 2 := by
  rw [Real.circleAverage_def]
  change (2 * Real.pi)⁻¹ *
    (∫ θ in (0:ℝ)..2 * Real.pi, (circleMap c ρ θ).im ^ 2) =
    c.im ^ 2 + ρ ^ 2 / 2
  have hmap (θ : ℝ) : (circleMap c ρ θ).im =
      c.im + ρ * Real.sin θ := by
    rw [show circleMap c ρ θ = c + circleMap 0 ρ θ from by simp [circleMap]]
    simp [Complex.add_im, circleMap_zero_im]
  simp_rw [hmap]
  have hpoly (θ : ℝ) :
      (c.im + ρ * Real.sin θ)^2 =
        c.im^2 + (2 * c.im * ρ) * Real.sin θ +
          ρ^2 * Real.sin θ^2 := by ring
  simp_rw [hpoly]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_sin, integral_sin_sq]
  · have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hcos : Real.cos (Real.pi * 2) = 1 := by
      convert Real.cos_two_pi using 1 <;> ring
    have hsin : Real.sin (Real.pi * 2) = 0 := by
      convert Real.sin_two_pi using 1 <;> ring
    field_simp <;> simp [Real.cos_two_pi, Real.sin_two_pi] <;> ring
  · exact (by fun_prop : Continuous _).intervalIntegrable _ _
  · exact (by fun_prop : Continuous _).intervalIntegrable _ _
  · exact (by fun_prop : Continuous _).intervalIntegrable _ _
  · exact (by fun_prop : Continuous _).intervalIntegrable _ _

end SpringerLean