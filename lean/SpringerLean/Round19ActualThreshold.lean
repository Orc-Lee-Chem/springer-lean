import SpringerLean.Round19ThresholdSet
import SpringerLean.Round19UpperLevel
import SpringerLean.Round17ActualCurve

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- Conditional first two steps of the paper's centered-arc argument.
The only extra premise is the still-open sign of the actual vertical
potential difference at the displayed threshold. -/
theorem regularExterior_projected_set_bound_of_vertical_sign
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (a : ℝ)
    (hsign : (∫ y : ℝ,
      regularExteriorVerticalPotentialDifference F s ξ a y) ≤ 0)
    (A : Set ℝ) (hA : MeasurableSet A) :
    (∫ θ in A,
      (conj ξ * rescaleExterior s F (circleMap 0 1 θ)).re
        ∂(volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) ≤
      a * (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).real A +
      (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        max (2 * (circleMap 0 1 θ).re - a) 0) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  haveI : IsFiniteMeasure μ := Real.isFiniteMeasure_restrict_Ioc 0 (2 * Real.pi)
  let X : ℝ → ℝ := fun θ =>
    (conj ξ * rescaleExterior s F (circleMap 0 1 θ)).re
  let V : ℝ → ℝ := fun θ => 2 * (circleMap 0 1 θ).re
  have hXc : Continuous X :=
    Complex.continuous_re.comp
      (regularExterior_rotated_angle_continuous F hc hs0 hs1 ξ)
  have hPc : Continuous (fun θ => max (X θ - a) 0) := by
    exact (hXc.sub continuous_const).max continuous_const
  have hX : Integrable X μ := by
    exact (hXc.continuousOn.integrableOn_compact (μ := volume)
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * Real.pi)))).mono_set Ioc_subset_Icc_self
  have hP : Integrable (fun θ => max (X θ - a) 0) μ := by
    exact (hPc.continuousOn.integrableOn_compact (μ := volume)
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * Real.pi)))).mono_set Ioc_subset_Icc_self
  have hfirst := setIntegral_le_threshold_add_positivePart X A hA hX a hP
  have hcomp := regularExterior_positivePart_le_of_vertical_sign
    F hc hs0 hs1 ξ a hsign
  rw [circleAverage_eq_angle_Ioc, circleAverage_eq_angle_Ioc] at hcomp
  have hfac : 0 < (2 * Real.pi)⁻¹ := by positivity
  have hsecond :
      (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi), max (X θ - a) 0) ≤
      ∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi), max (V θ - a) 0 := by
    exact le_of_mul_le_mul_left hcomp hfac
  change (∫ θ in A, X θ ∂μ) ≤
    a * μ.real A + ∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi), max (V θ - a) 0
  have hsecond' : (∫ θ : ℝ, max (X θ - a) 0 ∂μ) ≤
      ∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi), max (V θ - a) 0 := hsecond
  have hsum := add_le_add_left hsecond' (a * μ.real A)
  exact hfirst.trans (by simpa only [add_comm] using hsum)

/-- The regularized actual boundary is bounded by the comparator on its
superlevel set of the same angular mass. The vertical sign remains explicit. -/
theorem regularExterior_projected_set_le_comparator_superlevel_of_vertical_sign
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (a : ℝ)
    (hsign : (∫ y : ℝ,
      regularExteriorVerticalPotentialDifference F s ξ a y) ≤ 0)
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
          ∂(volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  haveI : IsFiniteMeasure μ := Real.isFiniteMeasure_restrict_Ioc 0 (2 * Real.pi)
  let V : ℝ → ℝ := fun θ => 2 * (circleMap 0 1 θ).re
  have hVc : Continuous V := by
    dsimp [V]
    fun_prop
  have hC : MeasurableSet {θ : ℝ | a ≤ V θ} :=
    measurableSet_Ici.preimage hVc.measurable
  have hV : Integrable V μ := by
    exact (hVc.continuousOn.integrableOn_compact (μ := volume)
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * Real.pi)))).mono_set Ioc_subset_Icc_self
  have hPc : Continuous (fun θ => max (V θ - a) 0) := by
    exact (hVc.sub continuous_const).max continuous_const
  have hP : Integrable (fun θ => max (V θ - a) 0) μ := by
    exact (hPc.continuousOn.integrableOn_compact (μ := volume)
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * Real.pi)))).mono_set Ioc_subset_Icc_self
  have hfirst := regularExterior_projected_set_bound_of_vertical_sign
    F hc hs0 hs1 ξ a hsign A hA
  have hident := integral_positivePart_eq_superlevel_sub
    (μ := μ) V a hC hV hP
  change (∫ θ in A,
    (conj ξ * rescaleExterior s F (circleMap 0 1 θ)).re ∂μ) ≤
      a * μ.real A + ∫ θ, max (V θ - a) 0 ∂μ at hfirst
  change μ.real A = μ.real {θ : ℝ | a ≤ V θ} at hmass
  rw [hident, hmass] at hfirst
  change (∫ θ in A,
    (conj ξ * rescaleExterior s F (circleMap 0 1 θ)).re ∂μ) ≤
      ∫ θ in {θ : ℝ | a ≤ V θ}, V θ ∂μ
  linarith

end SpringerLean
