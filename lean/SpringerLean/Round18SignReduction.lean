import SpringerLean.Round17VerticalActual

open MeasureTheory
open scoped ComplexConjugate

namespace SpringerLean

/-- The remaining potential-theoretic sign is exactly the boundary
positive-part inequality, at every real threshold. This is a conditional
interface: its sign premise is the still-open mathematical theorem. -/
theorem regularExterior_positivePart_le_of_vertical_sign
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (a : ℝ)
    (hsign : (∫ y : ℝ,
      regularExteriorVerticalPotentialDifference F s ξ a y) ≤ 0) :
    Real.circleAverage
      (fun ζ => max ((conj ξ * rescaleExterior s F ζ).re - a) 0) 0 1 ≤
    Real.circleAverage
      (fun ζ : ℂ => max (2 * ζ.re - a) 0) 0 1 := by
  rw [regularExteriorVerticalPotentialDifference_integral_posPart
    F hc hs0 hs1 ξ a] at hsign
  have hpi : 0 < 2 * Real.pi := by positivity
  have hsub : Real.circleAverage
      (fun ζ => max ((conj ξ * rescaleExterior s F ζ).re - a) 0) 0 1 -
    Real.circleAverage (fun ζ : ℂ => max (2 * ζ.re - a) 0) 0 1 ≤ 0 := by
    by_contra hh
    have hpos : 0 < Real.circleAverage
        (fun ζ => max ((conj ξ * rescaleExterior s F ζ).re - a) 0) 0 1 -
      Real.circleAverage (fun ζ : ℂ => max (2 * ζ.re - a) 0) 0 1 := lt_of_not_ge hh
    linarith [mul_pos hpi hpos]
  exact sub_nonpos.mp hsub

/-- Conversely, a positive-part comparison at one threshold gives the
sign of the actual-minus-comparison vertical potential integral there. -/
theorem regularExterior_vertical_sign_of_positivePart_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (a : ℝ)
    (hpos : Real.circleAverage
      (fun ζ => max ((conj ξ * rescaleExterior s F ζ).re - a) 0) 0 1 ≤
      Real.circleAverage
        (fun ζ : ℂ => max (2 * ζ.re - a) 0) 0 1) :
    (∫ y : ℝ, regularExteriorVerticalPotentialDifference F s ξ a y) ≤ 0 := by
  rw [regularExteriorVerticalPotentialDifference_integral_posPart
    F hc hs0 hs1 ξ a]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hpos)

end SpringerLean
