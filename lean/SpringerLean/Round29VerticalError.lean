import SpringerLean.Round29ReferenceVertical
import SpringerLean.Round28ActualPotentialContinuous
import SpringerLean.Round17VerticalActual

open MeasureTheory

namespace SpringerLean

/-- Both actual and comparison errors from the common radial reference are
integrable on each vertical line, with one shared quadratic dominator. -/
theorem regularExterior_reference_vertical_errors_integrable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a : ℝ) :
    Integrable (fun t : ℝ =>
      regularExteriorRotatedPotential F s ξ ((a : ℂ) + (t : ℂ) * Complex.I) -
        verticalReferenceKernel a t) ∧
    Integrable (fun t : ℝ =>
      comparisonSegmentPotential ((a : ℂ) + (t : ℂ) * Complex.I) -
        verticalReferenceKernel a t) := by
  obtain ⟨C, hC0, hbound⟩ :=
    regularExterior_potentials_reference_global_quadratic F hc hs0 hs1 ξ hξ
  let z : ℝ → ℂ := fun t => (a : ℂ) + (t : ℂ) * Complex.I
  let g : ℝ → ℝ := fun t => regularExteriorRotatedPotential F s ξ (z t) -
    verticalReferenceKernel a t
  let G : ℝ → ℝ := fun t => comparisonSegmentPotential (z t) -
    verticalReferenceKernel a t
  have hzcont : Continuous z := by fun_prop
  have hgcont : Continuous g :=
    (regularExterior_rotated_potential_continuous F hc hs0 hs1 ξ hξ).comp hzcont |>.sub
      (verticalReferenceKernel_continuous a)
  have hdom : Integrable (fun t : ℝ => C * (1 + a ^ 2 + t ^ 2)⁻¹) :=
    (verticalReferenceErrorKernel_integrable a).const_mul C
  have hpoint (t : ℝ) : |g t| + |G t| ≤ C * (1 + a ^ 2 + t ^ 2)⁻¹ := by
    have h := hbound (z t)
    rw [radialReferencePotential_vertical, vertical_complex_norm_sq] at h
    simpa only [g, G, z, div_eq_mul_inv, ← add_assoc] using h
  have hgint : Integrable g := by
    apply Integrable.mono' hdom hgcont.aestronglyMeasurable
    filter_upwards [] with t
    have h := hpoint t
    rw [Real.norm_eq_abs]
    have hG : 0 ≤ |G t| := abs_nonneg _
    linarith
  have hGint : Integrable G := by
    have hd : Integrable (regularExteriorVerticalPotentialDifference F s ξ a) :=
      regularExteriorVerticalPotentialDifference_integrable F hc hs0 hs1 ξ a
    have hident : G = g - regularExteriorVerticalPotentialDifference F s ξ a := by
      funext t
      dsimp [G, g, regularExteriorVerticalPotentialDifference,
        regularExteriorRotatedPotential, comparisonSegmentPotential]
      ring
    rw [hident]
    exact hgint.sub hd
  exact ⟨hgint, hGint⟩

/-- The total vertical reference errors decay at least as the exact Cauchy
kernel, uniformly over the height parameter in later applications. -/
theorem regularExterior_reference_vertical_errors_integral_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ,
      (∫ t : ℝ,
        |regularExteriorRotatedPotential F s ξ
           ((a : ℂ) + (t : ℂ) * Complex.I) - verticalReferenceKernel a t| +
         |comparisonSegmentPotential
           ((a : ℂ) + (t : ℂ) * Complex.I) - verticalReferenceKernel a t|) ≤
        C * Real.pi / Real.sqrt (1 + a ^ 2) := by
  obtain ⟨C, hC0, hbound⟩ :=
    regularExterior_potentials_reference_global_quadratic F hc hs0 hs1 ξ hξ
  refine ⟨C, hC0, ?_⟩
  intro a
  have hle (t : ℝ) :
      |regularExteriorRotatedPotential F s ξ
           ((a : ℂ) + (t : ℂ) * Complex.I) - verticalReferenceKernel a t| +
         |comparisonSegmentPotential
           ((a : ℂ) + (t : ℂ) * Complex.I) - verticalReferenceKernel a t| ≤
        C * (1 + a ^ 2 + t ^ 2)⁻¹ := by
    have h := hbound ((a : ℂ) + (t : ℂ) * Complex.I)
    rw [radialReferencePotential_vertical, vertical_complex_norm_sq] at h
    simpa only [div_eq_mul_inv, ← add_assoc] using h
  have hint := (regularExterior_reference_vertical_errors_integrable
    F hc hs0 hs1 ξ hξ a)
  have hL : Integrable (fun t : ℝ =>
      |regularExteriorRotatedPotential F s ξ
           ((a : ℂ) + (t : ℂ) * Complex.I) - verticalReferenceKernel a t| +
        |comparisonSegmentPotential
           ((a : ℂ) + (t : ℂ) * Complex.I) - verticalReferenceKernel a t|) :=
    hint.1.abs.add hint.2.abs
  have hR := (verticalReferenceErrorKernel_integrable a).const_mul C
  have hineq := integral_mono hL hR hle
  rw [integral_const_mul, verticalReferenceErrorKernel_integral] at hineq
  convert hineq using 1 <;> ring

end SpringerLean
