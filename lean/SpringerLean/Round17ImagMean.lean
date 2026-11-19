import SpringerLean.Round17RawPotential

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- The imaginary directional projection of the actual regularized
exterior boundary also has zero circle mean. -/
theorem rescaleExterior_imaginary_boundary_circleAverage_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ξ : ℂ) :
    Real.circleAverage
      (fun ζ : ℂ => (conj ξ * rescaleExterior s F ζ).im) 0 1 = 0 := by
  have hpoint (ζ : ℂ) :
      (conj (Complex.I * ξ) * rescaleExterior s F ζ).re =
        (conj ξ * rescaleExterior s F ζ).im := by
    simp [map_mul, Complex.mul_re, Complex.mul_im]
    ring
  have heq : (fun ζ : ℂ => (conj (Complex.I * ξ) * rescaleExterior s F ζ).re) =
      (fun ζ : ℂ => (conj ξ * rescaleExterior s F ζ).im) := by
    funext ζ
    exact hpoint ζ
  rw [← heq]
  exact rescaleExterior_projected_boundary_circleAverage_zero F hc hs0 hs1 (Complex.I * ξ)

/-- The same statement in the actual angle measure, before division by 2π. -/
theorem rescaleExterior_imaginary_angle_integral_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ξ : ℂ) :
    (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
      (conj ξ * rescaleExterior s F (circleMap 0 1 θ)).im) = 0 := by
  have h := rescaleExterior_imaginary_boundary_circleAverage_zero F hc hs0 hs1 ξ
  rw [circleAverage_eq_angle_Ioc] at h
  have hfac : (2 * Real.pi)⁻¹ ≠ 0 := by positivity
  exact (mul_eq_zero.mp h).resolve_left hfac

end SpringerLean
