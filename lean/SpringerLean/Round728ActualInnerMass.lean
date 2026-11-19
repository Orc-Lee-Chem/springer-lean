import SpringerLean.Round727ActualInnerTop
import SpringerLean.Round33CenteredArc
import SpringerLean.Round706AngularTopEndpointBounds

open MeasureTheory Set
open scoped ENNReal

namespace SpringerLean
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Both zero and full angular mass are included. -/
theorem actualHarmonic_projected_set_le_sine_of_raw_mass_closed
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ) (hcn : ‖c‖ = 1)
    {r h : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hh0 : 0 ≤ h) (hhpi : h ≤ Real.pi)
    (A : Set ℝ) (hAm : MeasurableSet A) (hAs : A ⊆ Ioc 0 (2*Real.pi))
    (hmass : volume A = ENNReal.ofReal (2*h)) :
    (∫ θ in A, (c*actualHarmonic F (circleMap 0 r θ)).re) ≤ 4*r*Real.sin h := by
  by_cases hzero : h = 0
  · have hz : volume A = 0 := by simpa only [hzero, mul_zero, ENNReal.ofReal_zero] using hmass
    rw [setIntegral_measure_zero _ hz]
    simp only [hzero, Real.sin_zero, mul_zero, le_refl]
  by_cases hfull : h = Real.pi
  · have hvI : volume (Ioc (0 : ℝ) (2*Real.pi)) = ENNReal.ofReal (2*Real.pi) := by
      rw [Real.volume_Ioc, sub_zero]
    have hae : A =ᵐ[volume] Ioc 0 (2*Real.pi) :=
      ae_eq_of_subset_of_measure_ge hAs (by rw [hmass, hfull, hvI])
        hAm.nullMeasurableSet (by rw [hvI]; finiteness)
    rw [setIntegral_congr_set hae,
      actualHarmonic_angular_projection_turn_integral_zero F hc c hr0 hr1]
    simp only [hfull, Real.sin_pi, mul_zero, le_refl]
  exact actualHarmonic_projected_set_le_sine_of_raw_mass F hc c hcn hr0 hr1
    (lt_of_le_of_ne hh0 (Ne.symm hzero)) (lt_of_le_of_ne hhpi hfull) A hAm hAs hmass

/-- Every actual projected set has an equal-mass comparator set with at
least its integral. Endpoint comparator sets are empty/full; proper
masses use the centered arc. All integrals use raw angle. -/
theorem actualHarmonic_projected_set_exists_comparator
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ) (hcn : ‖c‖ = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (A : Set ℝ) (hAm : MeasurableSet A) (hAs : A ⊆ Ioc 0 (2*Real.pi)) :
    ∃ B : Set ℝ, MeasurableSet B ∧ B ⊆ Ioc 0 (2*Real.pi) ∧ volume B = volume A ∧
      (∫ θ in A, (c*actualHarmonic F (circleMap 0 r θ)).re) ≤
        ∫ θ in B, 2*r*Real.cos θ := by
  let I : Set ℝ := Ioc 0 (2*Real.pi)
  let h : ℝ := volume.real A/2
  have hfin : volume A ≠ ∞ := ((Metric.isBounded_Ioc _ _).subset hAs).measure_lt_top.ne
  have hvI : volume.real I = 2*Real.pi := by
    rw [Measure.real_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (by positivity)]
  have hh0 : 0 ≤ h := by dsimp [h]; positivity
  have hhpi : h ≤ Real.pi := by
    have hv := measureReal_mono (μ := volume) hAs (Metric.isBounded_Ioc _ _).measure_lt_top.ne
    change volume.real A ≤ volume.real I at hv
    rw [hvI] at hv
    dsimp [h]
    linarith
  have hmass : volume A = ENNReal.ofReal (2*h) := by
    have heq : 2*h = volume.real A := by dsimp [h]; ring
    rw [heq, Measure.real_def, ENNReal.ofReal_toReal hfin]
  have hb := actualHarmonic_projected_set_le_sine_of_raw_mass_closed
    F hc c hcn hr0 hr1 hh0 hhpi A hAm hAs hmass
  by_cases hz : h = 0
  · refine ⟨∅, by measurability, empty_subset _, ?_, ?_⟩
    · simp only [measure_empty, hmass, hz, mul_zero, ENNReal.ofReal_zero]
    · simpa only [hz, Real.sin_zero, mul_zero, setIntegral_empty] using hb
  by_cases hf : h = Real.pi
  · refine ⟨I, measurableSet_Ioc, Subset.rfl, ?_, ?_⟩
    · rw [hmass, hf, Real.volume_Ioc, sub_zero]
    · have hzero : (∫ θ in I, 2*r*Real.cos θ) = 0 := by
        rw [show I = Ioc 0 (2*Real.pi) from rfl,
          ← intervalIntegral.integral_of_le (by positivity : 0 ≤ 2*Real.pi),
          intervalIntegral.integral_const_mul, integral_cos]
        simp only [Real.sin_two_pi, Real.sin_zero, sub_zero, mul_zero]
      rw [hzero]
      simpa only [hf, Real.sin_pi, mul_zero] using hb
  have hp : h < Real.pi := lt_of_le_of_ne hhpi hf
  refine ⟨centeredAngularArc h, measurableSet_Ioc.union measurableSet_Icc, ?_, ?_, ?_⟩
  · rw [← comparator_superlevel_inter_turn_eq_centeredAngularArc h hh0 hhpi]
    exact inter_subset_left
  · rw [centeredAngularArc_volume h hh0 hp, hmass]
  · have heq : (fun θ : ℝ => 2*r*Real.cos θ) = fun θ => r*(2*Real.cos θ) := by
      funext θ
      ring
    rw [heq, integral_const_mul, centeredAngularArc_comparator_integral h hh0 hp]
    nlinarith

end SpringerLean

#print axioms SpringerLean.actualHarmonic_projected_set_le_sine_of_raw_mass_closed
#print axioms SpringerLean.actualHarmonic_projected_set_exists_comparator
