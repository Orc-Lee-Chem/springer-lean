import SpringerLean.Round33CenteredArc

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- Sharp upper-quantile integral bound for the actual regularized boundary.
Here the input mass is raw angular length 2q, not probability mass q/π. -/
theorem regularExterior_projected_set_le_sine_of_raw_mass
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (q : ℝ) (hq0 : 0 ≤ q) (hqpi : q < Real.pi)
    (A : Set ℝ) (hA : MeasurableSet A)
    (hmass :
      (volume.restrict (Ioc (0:ℝ) (2 * Real.pi))).real A = 2*q) :
    (∫ θ in A,
      (conj ξ * rescaleExterior s F (circleMap 0 1 θ)).re
        ∂(volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) ≤
      4 * Real.sin q := by
  have hmass' :
      (volume.restrict (Ioc (0:ℝ) (2 * Real.pi))).real A =
      (volume.restrict (Ioc (0:ℝ) (2 * Real.pi))).real
        {θ : ℝ | 2 * Real.cos q ≤ 2 * (circleMap 0 1 θ).re} := by
    rw [hmass, comparator_superlevel_raw_angular_mass q hq0 hqpi]
  have h := regularExterior_projected_set_le_comparator_superlevel
    F hc hs0 hs1 ξ hξ (2 * Real.cos q) A hA hmass'
  rw [comparator_superlevel_raw_integral q hq0 hqpi] at h
  exact h

/-- Normalized form: probability mass m corresponds to raw angle 2πm. -/
theorem regularExterior_projected_set_normalized_quantile_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (m : ℝ) (hm0 : 0 ≤ m) (hm1 : m < 1)
    (A : Set ℝ) (hA : MeasurableSet A)
    (hmass :
      (volume.restrict (Ioc (0:ℝ) (2 * Real.pi))).real A /
        (2 * Real.pi) = m) :
    (2 * Real.pi)⁻¹ *
      (∫ θ in A,
        (conj ξ * rescaleExterior s F (circleMap 0 1 θ)).re
          ∂(volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) ≤
        2 * Real.sin (Real.pi * m) / Real.pi := by
  have hq0 : 0 ≤ Real.pi * m := mul_nonneg Real.pi_pos.le hm0
  have hqpi : Real.pi * m < Real.pi := by nlinarith [Real.pi_pos]
  have hraw :
      (volume.restrict (Ioc (0:ℝ) (2 * Real.pi))).real A =
        2 * (Real.pi * m) := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp at hmass
    nlinarith
  have h := regularExterior_projected_set_le_sine_of_raw_mass
    F hc hs0 hs1 ξ hξ (Real.pi * m) hq0 hqpi A hA hraw
  have hfactor : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  have h' := mul_le_mul_of_nonneg_left h hfactor
  convert h' using 1 <;> field_simp <;> ring
end SpringerLean