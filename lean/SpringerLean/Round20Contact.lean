import SpringerLean.Round20ProjectionRange
import SpringerLean.Round18CompactSupport
import SpringerLean.Round14PotentialBoundary

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- A positive vertical potential difference forces the threshold to be an
actual projected boundary value. The range-endpoint sign theorems rule out
both complementary possibilities. -/
theorem regularExterior_projection_exists_eq_of_vertical_integral_pos
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (a : ℝ)
    (hpos : 0 < (∫ y : ℝ,
      regularExteriorVerticalPotentialDifference F s ξ a y)) :
    ∃ ζ ∈ sphere (0 : ℂ) 1,
      (conj ξ * rescaleExterior s F ζ).re = a := by
  let X : ℂ → ℝ := fun ζ =>
    (conj ξ * rescaleExterior s F ζ).re
  have hnotupper : ¬ ∀ ζ ∈ sphere (0 : ℂ) 1, X ζ ≤ a := by
    intro hupper
    have h := regularExteriorVerticalPotentialDifference_integral_le_zero_of_upper
      F hc hs0 hs1 ξ a hupper
    linarith
  have hnotlower : ¬ ∀ ζ ∈ sphere (0 : ℂ) 1, a ≤ X ζ := by
    intro hlower
    have h := regularExteriorVerticalPotentialDifference_integral_le_zero_of_lower
      F hc hs0 hs1 ξ a hlower
    linarith
  push Not at hnotupper hnotlower
  obtain ⟨hi, hhi, hhi'⟩ := hnotupper
  obtain ⟨lo, hlo, hlo'⟩ := hnotlower
  have hpre : IsPreconnected (sphere (0 : ℂ) 1) :=
    isPreconnected_sphere (by simp) (0 : ℂ) 1
  have hcont : ContinuousOn X (sphere (0 : ℂ) 1) :=
    regularExterior_projection_continuousOn_sphere F hc hs0 hs1 ξ
  obtain ⟨ζ, hζ, hζeq⟩ := hpre.intermediate_value₂
    hlo hhi hcont continuousOn_const (le_of_lt hlo') (le_of_lt hhi')
  exact ⟨ζ, hζ, hζeq⟩

/-- At a positive vertical threshold, the rotated actual boundary potential
vanishes at a point on that vertical line. -/
theorem regularExterior_rotated_boundary_potential_zero_of_vertical_integral_pos
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a : ℝ)
    (hpos : 0 < (∫ y : ℝ,
      regularExteriorVerticalPotentialDifference F s ξ a y)) :
    ∃ t₀ : ℝ,
      Real.circleAverage
        (fun ζ : ℂ => Real.log ‖((a : ℂ) + (t₀ : ℂ) * Complex.I) -
          conj ξ * rescaleExterior s F ζ‖) 0 1 = 0 := by
  obtain ⟨v, hv, hvre⟩ :=
    regularExterior_projection_exists_eq_of_vertical_integral_pos
      F hc hs0 hs1 ξ a hpos
  let W : ℂ := conj ξ * rescaleExterior s F v
  refine ⟨W.im, ?_⟩
  have hpoint : ((a : ℂ) + (W.im : ℂ) * Complex.I) = W := by
    rw [← hvre]
    exact Complex.re_add_im W
  have hvnorm : ‖v‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using hv
  have hzero := regularExterior_curve_boundary_log_potential_zero
    F hc hs0 hs1 hvnorm
  calc
    Real.circleAverage
        (fun ζ : ℂ => Real.log ‖((a : ℂ) + (W.im : ℂ) * Complex.I) -
          conj ξ * rescaleExterior s F ζ‖) 0 1 =
      Real.circleAverage
        (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ -
          rescaleExterior s F v‖) 0 1 := by
            apply Real.circleAverage_congr_sphere
            intro ζ _
            rw [hpoint]
            change Real.log ‖conj ξ * rescaleExterior s F v -
              conj ξ * rescaleExterior s F ζ‖ =
                Real.log ‖rescaleExterior s F ζ - rescaleExterior s F v‖
            rw [← mul_sub, norm_mul,
              Complex.norm_conj, hξ, one_mul, norm_sub_rev]
    _ = 0 := hzero

end SpringerLean
