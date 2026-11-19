import SpringerLean.Round728ActualInnerMass
import SpringerLean.Round19UpperLevel
import SpringerLean.Round27DoubleCircle

open MeasureTheory Set

namespace SpringerLean
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- All actual inner-circle positive-part tests, with comparator 2r cos. -/
theorem actualHarmonic_inner_positivePart_angle_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ) (hcn : ‖c‖ = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (a : ℝ) :
    (∫ θ in Ioc (0 : ℝ) (2*Real.pi),
      max ((c*actualHarmonic F (circleMap 0 r θ)).re-a) 0) ≤
      ∫ θ in Ioc (0 : ℝ) (2*Real.pi), max (2*r*Real.cos θ-a) 0 := by
  let I : Set ℝ := Ioc 0 (2*Real.pi)
  let μ : Measure ℝ := volume.restrict I
  haveI : IsFiniteMeasure μ := Real.isFiniteMeasure_restrict_Ioc 0 (2*Real.pi)
  let X : ℝ → ℝ := fun θ => (c*actualHarmonic F (circleMap 0 r θ)).re
  let Y : ℝ → ℝ := fun θ => 2*r*Real.cos θ
  have hXc : Continuous X := (actualHarmonic_angular_projection_analytic F hc c hr0 hr1).continuous
  have hYc : Continuous Y := by dsimp [Y]; fun_prop
  have hi (Z : ℝ → ℝ) (hZ : Continuous Z) : Integrable Z μ :=
    (hZ.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hX : Integrable X μ := hi X hXc
  have hY : Integrable Y μ := hi Y hYc
  have hPX : Integrable (fun θ => max (X θ-a) 0) μ :=
    hi _ ((hXc.sub continuous_const).max continuous_const)
  have hPY : Integrable (fun θ => max (Y θ-a) 0) μ :=
    hi _ ((hYc.sub continuous_const).max continuous_const)
  let S : Set ℝ := {θ | a ≤ X θ}
  let A : Set ℝ := I ∩ S
  have hSm : MeasurableSet S := measurableSet_Ici.preimage hXc.measurable
  have hAm : MeasurableSet A := measurableSet_Ioc.inter hSm
  obtain ⟨B, hBm, hBs, hmass, hbound⟩ :=
    actualHarmonic_projected_set_exists_comparator F hc c hcn hr0 hr1 A hAm inter_subset_left
  have hAeq : μ S = volume A := by
    dsimp [μ, A]
    rw [Measure.restrict_apply hSm, inter_comm]
  have hBeq : μ B = volume B := by
    dsimp [μ]
    rw [Measure.restrict_apply hBm, inter_eq_left.mpr hBs]
  have hreal : μ.real B = μ.real S := by rw [Measure.real_def, Measure.real_def, hBeq, hmass, hAeq]
  have hSX : (∫ θ in S, X θ ∂μ) = ∫ θ in A, X θ := by
    dsimp [μ, A]
    rw [Measure.restrict_restrict hSm, inter_comm]
  have hBY : (∫ θ in B, Y θ ∂μ) = ∫ θ in B, Y θ := by
    dsimp [μ]
    rw [Measure.restrict_restrict_of_subset hBs]
  have hpos := integral_positivePart_eq_superlevel_sub X a hSm hX hPX
  change (∫ θ, max (X θ-a) 0 ∂μ) = (∫ θ in S, X θ ∂μ)-a*μ.real S at hpos
  have hthreshold := setIntegral_le_threshold_add_positivePart Y B hBm hY a hPY
  rw [hreal, hBY] at hthreshold
  rw [hpos, hSX]
  change (∫ θ in A, X θ)-a*μ.real S ≤ ∫ θ, max (Y θ-a) 0 ∂μ
  change (∫ θ in A, X θ) ≤ ∫ θ in B, Y θ at hbound
  linarith

/-- Radial pullback preserves the same angular probability measure. -/
theorem circleAverage_mul_radius_zero (f : ℂ → ℝ) (r : ℝ) :
    Real.circleAverage (fun ζ => f ((r : ℂ)*ζ)) 0 1 = Real.circleAverage f 0 r := by
  rw [circleAverage_eq_angle_Ioc_general, circleAverage_eq_angle_Ioc_general]
  have hm (θ : ℝ) : (r : ℂ)*circleMap 0 1 θ = circleMap 0 r θ := by simp [circleMap_zero]
  simp_rw [hm]

theorem actualHarmonic_inner_positivePart_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ) (hcn : ‖c‖ = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (a : ℝ) :
    Real.circleAverage
      (fun ζ => max ((c*actualHarmonic F ((r : ℂ)*ζ)).re-a) 0) 0 1 ≤
      Real.circleAverage (fun ζ : ℂ => max (2*r*ζ.re-a) 0) 0 1 := by
  have hb := actualHarmonic_inner_positivePart_angle_le F hc c hcn hr0 hr1 a
  rw [circleAverage_eq_angle_Ioc, circleAverage_eq_angle_Ioc]
  have hm (θ : ℝ) : (r : ℂ)*circleMap 0 1 θ = circleMap 0 r θ := by simp [circleMap_zero]
  simp_rw [hm, circleMap_zero_re, one_mul]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

end SpringerLean

#print axioms SpringerLean.actualHarmonic_inner_positivePart_angle_le
#print axioms SpringerLean.circleAverage_mul_radius_zero
#print axioms SpringerLean.actualHarmonic_inner_positivePart_le
