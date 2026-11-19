import SpringerLean.Round32VerticalSign
import SpringerLean.Round18ActualFiniteConvex
import SpringerLean.Round19ActualThreshold

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- Unconditional positive-part comparison for each actual regularized boundary. -/
theorem regularExterior_positivePart_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a : ℝ) :
    Real.circleAverage
      (fun ζ => max ((conj ξ * rescaleExterior s F ζ).re - a) 0) 0 1 ≤
    Real.circleAverage
      (fun ζ : ℂ => max (2 * ζ.re - a) 0) 0 1 :=
  regularExterior_positivePart_le_of_vertical_sign F hc hs0 hs1 ξ a
    (regularExterior_vertical_potential_difference_integral_nonpos
      F hc hs0 hs1 ξ hξ a)

/-- Every finite convex hinge test of the actual regularized boundary. -/
theorem regularExterior_finiteHingeTest_le
    {ι : Type*} (S : Finset ι) (w t : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (p q : ℝ) :
    Real.circleAverage
      (fun ζ => finiteHingeTest S w t p q
        ((conj ξ * rescaleExterior s F ζ).re)) 0 1 ≤
    Real.circleAverage
      (fun ζ : ℂ => finiteHingeTest S w t p q (2 * ζ.re)) 0 1 :=
  regularExterior_finiteHingeTest_le_of_vertical_sign
    S w t hw F hc hs0 hs1 ξ
      (fun a => regularExterior_vertical_potential_difference_integral_nonpos
        F hc hs0 hs1 ξ hξ a) p q

/-- The actual projected integral bound for any measurable angular set. -/
theorem regularExterior_projected_set_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a : ℝ)
    (A : Set ℝ) (hA : MeasurableSet A) :
    (∫ θ in A,
      (conj ξ * rescaleExterior s F (circleMap 0 1 θ)).re
        ∂(volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) ≤
      a * (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).real A +
      (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        max (2 * (circleMap 0 1 θ).re - a) 0) :=
  regularExterior_projected_set_bound_of_vertical_sign
    F hc hs0 hs1 ξ a
      (regularExterior_vertical_potential_difference_integral_nonpos
        F hc hs0 hs1 ξ hξ a) A hA

/-- Equal-mass actual set comparison with the comparator's upper level set. -/
theorem regularExterior_projected_set_le_comparator_superlevel
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a : ℝ)
    (A : Set ℝ) (hA : MeasurableSet A)
    (hmass :
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).real A =
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).real
          {θ : ℝ | a ≤ 2 * (circleMap 0 1 θ).re}) :
    (∫ θ in A,
      (conj ξ * rescaleExterior s F (circleMap 0 1 θ)).re
        ∂(volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) ≤
      ∫ θ in {θ : ℝ | a ≤ 2 * (circleMap 0 1 θ).re},
        2 * (circleMap 0 1 θ).re
          ∂(volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
  regularExterior_projected_set_le_comparator_superlevel_of_vertical_sign
    F hc hs0 hs1 ξ a
      (regularExterior_vertical_potential_difference_integral_nonpos
        F hc hs0 hs1 ξ hξ a) A hA hmass

end SpringerLean